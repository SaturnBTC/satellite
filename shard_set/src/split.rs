//! Helpers to **redistribute remaining liquidity** (BTC or Rune) across a
//! **selected** set of shards after user-funded inputs and fees have already
//! been applied.
//!
//! This module is **purely functional**: it contains algorithms that *calculate*
//! balanced allocations or *extend* the in-flight
//! [`satellite_bitcoin::TransactionBuilder`].  *It never mutates the
//! on-chain shard accounts directly.*  State changes are ultimately carried
//! out by the higher-level wrappers on [`ShardSet`] which borrow the underlying
//! [`AccountLoader`]s only for the minimum time required.
//!
//! High-level BTC redistribution flow
//! ==================================
//! 1. [`compute_unsettled_btc_in_shards`] – sums the satoshis still owned by the
//!    selected shards (minus already-removed liquidity & fees).
//! 2. [`plan_btc_distribution_among_shards`] – derives an as-even-as-possible
//!    per-shard allocation while respecting the Bitcoin dust limit and, when
//!    the `utxo-consolidation` feature is active, marks consolidation inputs.
//! 3. [`redistribute_remaining_btc_to_shards`] – appends one change output per
//!    shard to the transaction.
//!
//! Rune helpers follow the same pattern behind the `runes` feature flag
//! (`compute_unsettled_rune_in_shards`, `plan_rune_distribution_among_shards`,
//! `redistribute_remaining_rune_to_shards`).
//!
//! Type parameters & generics
//! -------------------------
//! Most public functions are generic over the following compile-time bounds:
//! * `MAX_MODIFIED_ACCOUNTS` – maximum user-provided inputs accepted by the
//!   transaction builder.
//! * `MAX_INPUTS_TO_SIGN` – upper limit on shards per program instance.
//! * `MAX_SELECTED` – upper limit on simultaneously *selected* shards.
//! * `RS`, `U`, `S` – concrete types implementing the required Saturn traits.
//!
//! Error semantics
//! ---------------
//! * **Arithmetic overflow / underflow** ⇒ [`satellite_bitcoin::MathError`]
//! * **Rune-specific validation errors** ⇒ [`crate::StateShardError`]
//!
//! All algorithms are `no_std`-compatible and rely on the fixed-size
//! collections from `satellite_bitcoin`, keeping worst-case memory usage
//! bounded at compile time.
use std::cell::Ref;

use arch_program::{
    msg,
    rune::{RuneAmount, RuneId},
    utxo::UtxoMeta,
};
use bitcoin::{Amount, ScriptBuf, TxOut};
use satellite_bitcoin::generic::fixed_set::FixedCapacitySet;
use satellite_bitcoin::generic::fixed_set::FixedSet;
use satellite_bitcoin::{
    constants::DUST_LIMIT, fee_rate::FeeRate, utxo_info::UtxoInfoTrait, TransactionBuilder,
};
use satellite_bitcoin::{safe_add, safe_div, safe_mul, safe_sub, MathError};

use super::error::StateShardError;
use super::StateShard;

#[cfg(feature = "runes")]
use ordinals::Edict;

use satellite_lang::prelude::Owner;
use satellite_lang::ZeroCopy;

/// Errors specific to distribution and dust handling logic in this module.
#[derive(Debug, PartialEq)]
pub enum DistributionError {
    /// Total amount to distribute is non-zero but below the dust limit.
    TotalBelowDustLimit,
    /// Wrapper around generic math errors encountered during redistribution.
    Math(MathError),
}

impl From<MathError> for DistributionError {
    fn from(value: MathError) -> Self {
        DistributionError::Math(value)
    }
}

/// Redistributes the *remaining* satoshi value belonging to the provided shards
/// back into brand-new outputs (one per **retained allocation** after
/// dust-limit filtering) to achieve optimal liquidity balance across all
/// participating shards.
///
/// This function performs the complete BTC redistribution workflow:
/// 1. **Calculate remaining value**: Determines how many satoshis are still owned
///    by the shards **after** the caller has removed some liquidity
///    (`removed_from_shards`) and the program has paid transaction fees.
/// 2. **Plan optimal distribution**: Uses [`plan_btc_distribution_among_shards`]
///    to derive an as-even-as-possible per-shard allocation that respects the
///    Bitcoin dust limit.
/// 3. **Create transaction outputs**: Appends one [`TxOut`] to the underlying
///    transaction for every computed allocation, using `program_script_pubkey`
///    to lock those outputs back to the program.
///
/// # Output Ordering and Filtering
///
/// The returned vector contains **one element for each output actually created**
/// after dust filtering and is **sorted in descending order by amount (largest
/// first)** for deterministic behavior. When allocations below the dust limit
/// are removed, the length of the vector—and therefore the number of newly
/// created change outputs—can be **smaller than the number of selected shards**.
///
/// Since the order no longer corresponds to the indices returned by
/// [`ShardSet::selected_indices`], callers that need to map values back to
/// specific shards must perform that mapping explicitly.
///
/// # Type Parameters
/// * `MAX_MODIFIED_ACCOUNTS` – Maximum number of user-supplied UTXOs supported by
///   the [`TransactionBuilder`].
/// * `MAX_INPUTS_TO_SIGN` – Compile-time bound on the number of shards in a
///   single program instance.
/// * `RS` – Rune set type implementing [`FixedCapacitySet<Item = RuneAmount>`].
/// * `U` – UTXO info type implementing [`UtxoInfoTrait<RS>`].
/// * `S` – Shard type implementing [`StateShard<U, RS>`], [`ZeroCopy`], and [`Owner`].
///
/// # Parameters
/// * `tx_builder` – Mutable reference to the transaction currently being assembled.
/// * `selected_shards` – Slice of mutable shard references in the *Selected* state;
///   only these shards participate in the redistribution.
/// * `removed_from_shards` – Total satoshis that the caller already withdrew
///   from the selected shards during the current instruction.
/// * `program_script_pubkey` – Script that will lock the change outputs
///   produced by this function (usually the program's own script).
/// * `fee_rate` – Fee rate used to calculate how many satoshis were paid by the
///   program for transaction fees.
///
/// # Returns
/// A vector of `u128` values representing the satoshi amounts for each created
/// output, sorted in descending order. The sum of all values equals the total
/// redistributed amount.
///
/// # Errors
/// * [`MathError`] – If any safe-math operation overflows or underflows during
///   amount calculations or distribution planning.
///
/// # Example Scenarios
/// * **Equal distribution**: If 3 shards each have 1000 sats and 3000 sats need
///   redistribution, each gets 1000 sats.
/// * **Dust filtering**: If redistribution would create outputs below the dust
///   limit, those amounts are consolidated into larger outputs.
/// * **Uneven remainders**: Extra satoshis from modulo operations are distributed
///   evenly with preference given to earlier outputs.
#[allow(clippy::too_many_arguments)]
pub fn redistribute_remaining_btc_to_shards<
    'info,
    const MAX_MODIFIED_ACCOUNTS: usize,
    const MAX_INPUTS_TO_SIGN: usize,
    RS,
    U,
    S,
>(
    tx_builder: &mut TransactionBuilder<MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN, RS>,
    selected_shards: &[Ref<'info, S>],
    removed_from_shards: u64,
    program_script_pubkey: &ScriptBuf,
    fee_rate: &FeeRate,
) -> Result<Vec<u128>, DistributionError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    let remaining_amount = compute_unsettled_btc_in_shards(
        tx_builder,
        selected_shards,
        removed_from_shards,
        fee_rate,
    )?;

    let mut distribution =
        plan_btc_distribution_among_shards(tx_builder, selected_shards, remaining_amount as u128)?;

    // Largest first for deterministic ordering.
    distribution.sort_by(|a, b| b.cmp(a));

    for amount in distribution.iter() {
        let txout = TxOut {
            value: Amount::from_sat(*amount as u64),
            script_pubkey: program_script_pubkey.clone(),
        };

        tx_builder.transaction.output.push(txout);
    }

    Ok(distribution)
}

/// Sums the BTC value of shard-owned UTXOs that this transaction spends and
/// subtracts the fees paid by the program and any amounts already removed from
/// the shards to produce the unsettled amount.
///
/// Notes:
/// * Only shard-owned UTXOs that appear as inputs in the current transaction are
///   included in the sum.
/// * Program-paid fees are subtracted when applicable (feature-gated via
///   `utxo-consolidation`).
/// * Amounts already withdrawn from the selected shards during this instruction
///   (`removed_from_shards`) are also subtracted.
pub fn compute_unsettled_btc_in_shards<
    'info,
    const MAX_MODIFIED_ACCOUNTS: usize,
    const MAX_INPUTS_TO_SIGN: usize,
    RS,
    U,
    S,
>(
    tx_builder: &TransactionBuilder<MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN, RS>,
    selected_shards: &[Ref<'info, S>],
    removed_from_shards: u64,
    fee_rate: &FeeRate,
) -> Result<u64, MathError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    // ---------------------------------------------------------------------
    // 2. Sum the value of every shard-managed UTXO that appears in the set.
    // ---------------------------------------------------------------------
    let mut total_btc_amount: u64 = 0;

    for shard in selected_shards.iter() {
        let mut sum: u64 = 0;
        for utxo in shard.btc_utxos().iter() {
            for input in tx_builder.transaction.input.iter() {
                let spent_meta =
                    UtxoMeta::from_outpoint(input.previous_output.txid, input.previous_output.vout);
                if spent_meta == *utxo.meta() {
                    sum = sum.saturating_add(utxo.value());
                }
            }
        }

        total_btc_amount = safe_add(total_btc_amount, sum)?;
    }

    let fee_paid_by_program = {
        #[cfg(feature = "utxo-consolidation")]
        {
            tx_builder.get_fee_paid_by_program(fee_rate)
        }
        #[cfg(not(feature = "utxo-consolidation"))]
        {
            0
        }
    };

    let remaining_amount = safe_sub(
        safe_sub(total_btc_amount, removed_from_shards)?,
        fee_paid_by_program,
    )?;

    Ok(remaining_amount)
}

/// Plans an optimal BTC distribution across selected shards while respecting
/// the Bitcoin dust limit and ensuring no value is lost.
///
/// This internal helper function splits the given `amount` of satoshis across
/// the provided shards as evenly as possible, then applies dust limit filtering
/// to ensure all outputs meet Bitcoin's minimum value requirements.
///
/// The function delegates the core balancing logic to [`balance_amount_across_shards`]
/// and then applies [`redistribute_sub_dust_values`] to handle allocations below
/// the dust threshold.
///
/// # Type Parameters
/// * `MAX_MODIFIED_ACCOUNTS` – Maximum number of user-supplied UTXOs in the transaction.
/// * `MAX_INPUTS_TO_SIGN` – Maximum number of shards per program instance.
/// * `RS` – Rune set type implementing [`FixedCapacitySet<Item = RuneAmount>`].
/// * `U` – UTXO info type implementing [`UtxoInfoTrait<RS>`].
/// * `S` – Shard type implementing [`StateShard<U, RS>`], [`ZeroCopy`], and [`Owner`].
///
/// # Parameters
/// * `tx_builder` – Reference to the transaction builder for context.
/// * `selected_shards` – Slice of selected shards to distribute value among.
/// * `amount` – Total satoshis to distribute across the shards.
///
/// # Returns
/// A vector of `u128` values representing the final allocation per output after
/// dust filtering. The vector may be shorter than the number of input shards if
/// some allocations were below the dust limit and consolidated.
///
/// # Errors
/// * [`MathError`] – If any arithmetic operation overflows or underflows during
///   the distribution calculation or dust redistribution process.
///
/// # Dust Handling
/// Allocations below [`DUST_LIMIT`] are automatically:
/// 1. Removed from the output vector
/// 2. Aggregated into a single sum
/// 3. Redistributed evenly among the remaining valid allocations
/// 4. If no allocations remain above dust but the total exceeds dust, a single
///    output containing the full amount is created
fn plan_btc_distribution_among_shards<
    'info,
    const MAX_MODIFIED_ACCOUNTS: usize,
    const MAX_INPUTS_TO_SIGN: usize,
    RS,
    U,
    S,
>(
    tx_builder: &TransactionBuilder<MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN, RS>,
    selected_shards: &[Ref<'info, S>],
    amount: u128,
) -> Result<Vec<u128>, DistributionError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    let mut result = balance_amount_across_shards(
        tx_builder,
        selected_shards,
        &RuneAmount {
            id: RuneId::BTC,
            amount,
        },
    )?;

    redistribute_sub_dust_values(&mut result, DUST_LIMIT as u128)?;
    Ok(result)
}

/// Computes an optimal balanced allocation of the specified amount across the
/// provided shards without mutating any state.
///
/// This pure calculation function implements a sophisticated balancing algorithm
/// that aims to equalize holdings across all selected shards after the
/// redistribution is complete. The algorithm considers existing balances and
/// attempts to achieve equal per-shard totals when possible.
///
/// # Algorithm Overview
/// 1. **Current balance calculation**: Determines existing liquidity (BTC or Rune)
///    for each shard, excluding any UTXOs already being spent in the transaction.
/// 2. **Target balance derivation**: Calculates the ideal per-shard value that
///    would result in perfect equality after redistribution.
/// 3. **Need-based allocation**: If sufficient funds are available, each shard
///    receives exactly what it needs to reach the target balance, with any
///    leftover distributed evenly.
/// 4. **Proportional fallback**: If insufficient funds exist for perfect balance,
///    the available amount is distributed proportionally based on each shard's
///    individual need.
///
/// # Type Parameters
/// * `MAX_MODIFIED_ACCOUNTS` – Maximum number of user-supplied UTXOs in the transaction.
/// * `MAX_INPUTS_TO_SIGN` – Maximum number of shards per program instance.
/// * `RS` – Rune set type implementing [`FixedCapacitySet<Item = RuneAmount>`].
/// * `U` – UTXO info type implementing [`UtxoInfoTrait<RS>`].
/// * `S` – Shard type implementing [`StateShard<U, RS>`], [`ZeroCopy`], and [`Owner`].
///
/// # Parameters
/// * `tx_builder` – Reference to the transaction builder to check which UTXOs
///   are already being spent.
/// * `selected_shards` – Slice of selected shards to balance the amount across.
/// * `rune_amount` – The amount to distribute, specified as a [`RuneAmount`] where
///   `RuneId::BTC` indicates Bitcoin satoshis and other IDs indicate Rune tokens.
///
/// # Returns
/// A vector where the i-th element represents the allocation for the i-th
/// selected shard. The vector length always equals `selected_shards.len()` and
/// the sum of all entries equals `rune_amount.amount` (modulo rounding in
/// proportional scenarios).
///
/// # Errors
/// * [`MathError::Overflow`] – If intermediate calculations exceed numeric limits.
/// * [`MathError::Underflow`] – If subtraction operations go below zero.
/// * [`MathError::DivisionOverflow`] – If division by zero occurs (e.g., empty shard list).
///
/// # Invariants
/// * **Length preservation**: Output vector length always equals input shard count.
/// * **Value conservation**: Sum of allocations equals input amount (within rounding).
/// * **Non-negativity**: All allocation values are non-negative.
///
/// # Example
/// Given shards with balances [100, 200, 300] and 150 to distribute:
/// - Target per-shard: (100+200+300+150)/3 = 250
/// - Needs: [150, 50, 0] (to reach 250 each)
/// - Result: [150, 0, 0] (insufficient funds for full balancing)
fn balance_amount_across_shards<
    'info,
    const MAX_MODIFIED_ACCOUNTS: usize,
    const MAX_INPUTS_TO_SIGN: usize,
    RS,
    U,
    S,
>(
    tx_builder: &TransactionBuilder<MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN, RS>,
    selected_shards: &[Ref<'info, S>],
    rune_amount: &RuneAmount,
) -> Result<Vec<u128>, MathError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    let num_shards = selected_shards.len();

    // Allocate result vectors on the stack.
    let mut assigned_amounts: Vec<u128> = Vec::with_capacity(num_shards);
    let mut total_current_amount: u128 = 0;

    // --------------------------------------------------
    // Pre-compute the set of metas already used by the tx
    // --------------------------------------------------
    type InputMetaSet<const CAP: usize> = FixedSet<UtxoMeta, CAP>;
    let mut used_metas: InputMetaSet<MAX_INPUTS_TO_SIGN> = InputMetaSet::default();
    for input in tx_builder.transaction.input.iter() {
        let meta = UtxoMeta::from_outpoint(input.previous_output.txid, input.previous_output.vout);
        let _ = used_metas.insert(meta);
    }

    // 1. Determine the current amount per shard and overall.
    for shard in selected_shards.iter() {
        let current_res = match rune_amount.id {
            RuneId::BTC => shard
                .btc_utxos()
                .iter()
                .filter_map(|u| {
                    if used_metas.contains(u.meta()) {
                        None
                    } else {
                        Some(u.value() as u128)
                    }
                })
                .sum(),
            _ => {
                #[cfg(feature = "runes")]
                {
                    shard
                        .rune_utxo()
                        .and_then(|u| u.runes().find(&rune_amount.id).map(|r| r.amount))
                        .unwrap_or(0)
                }
                #[cfg(not(feature = "runes"))]
                {
                    0
                }
            }
        };

        assigned_amounts.push(current_res);
        total_current_amount = safe_add(total_current_amount, current_res)?;
    }

    msg!("total_current_amount: {}", total_current_amount);

    // Determine target per-shard balance.
    let total_after = safe_add(total_current_amount, rune_amount.amount)?;
    let desired_per_shard = safe_div(total_after, num_shards as u128)?;

    msg!("desired_per_shard: {}", desired_per_shard);

    // Calculate additional amount needed per shard to reach desired balance.
    let mut total_needed = 0u128;
    for current in assigned_amounts.iter_mut() {
        let needed = if desired_per_shard > *current {
            safe_sub(desired_per_shard, *current)?
        } else {
            0
        };
        total_needed = safe_add(total_needed, needed)?;
        *current = needed;
    }

    if total_needed <= rune_amount.amount {
        // Distribute leftover evenly across shards.
        let leftover = safe_sub(rune_amount.amount, total_needed)?;
        let per_shard_extra = safe_div(leftover, num_shards as u128)?;
        let mut extra_left = leftover % num_shards as u128;

        for amt in assigned_amounts.iter_mut() {
            *amt = safe_add(*amt, per_shard_extra)?;
            if extra_left > 0 {
                *amt = safe_add(*amt, 1)?;
                extra_left -= 1;
            }
        }
    } else {
        // Not enough to reach equal balance – scale proportionally.
        let mut cumulative = 0u128;
        let mut cumulative_needed = 0u128;

        for i in 0..num_shards {
            let needed = assigned_amounts[i];
            cumulative_needed = safe_add(cumulative_needed, needed)?;
            let proportional = safe_mul(rune_amount.amount, cumulative_needed)? / total_needed;
            assigned_amounts[i] = safe_sub(proportional, cumulative)?;
            cumulative = proportional;
        }
    }

    msg!("assigned_amounts: {:?}", assigned_amounts);
    Ok(assigned_amounts)
}

/// Redistributes amounts below the dust limit to prevent value loss and ensure
/// all outputs meet Bitcoin's minimum value requirements.
///
/// This function implements a dust consolidation algorithm that:
/// 1. **Aggregates sub-dust amounts**: Sums all allocations below `dust_limit`
/// 2. **Removes dust entries**: Filters out sub-dust allocations from the vector
/// 3. **Redistributes dust value**: Distributes the aggregated dust evenly among
///    remaining valid allocations
/// 4. **Handles edge cases**: Creates a single output if only dust exists but
///    the total exceeds the limit
///
/// The redistribution ensures that no satoshis are lost while maintaining
/// compliance with Bitcoin's dust limit rules. If the total of all sub-dust
/// amounts is itself above the dust limit, it forms a single consolidated output.
///
/// # Parameters
/// * `amounts` – Mutable vector of allocation amounts to process. Modified in-place.
/// * `dust_limit` – Minimum value threshold below which outputs are considered dust.
///
/// # Returns
/// * `Ok(())` – If redistribution completed successfully
/// * `Err(MathError)` – If arithmetic operations overflow during redistribution
///
/// # Algorithm Details
/// For remaining amounts after dust removal:
/// - Each gets `floor(dust_sum / remaining_count)` additional value
/// - Remainder from integer division is distributed one unit at a time to
///   the first `remainder` outputs
///
/// # Examples
/// ```text
/// Input: [1000, 200, 300, 2000], dust_limit: 546
/// Sub-dust: 200 + 300 = 500
/// Remaining: [1000, 2000]
/// Final: [1250, 2250] (500 distributed evenly)
/// ```
///
/// ```text
/// Input: [200, 300, 100], dust_limit: 546  
/// Sub-dust: 600 (>= dust_limit)
/// Final: [600] (single consolidated output)
/// ```
fn redistribute_sub_dust_values(
    amounts: &mut Vec<u128>,
    dust_limit: u128,
) -> Result<(), DistributionError> {
    // 0. If the total amount to distribute is non-zero but below dust, return an error
    //    to avoid silently losing value by producing no valid outputs.
    let mut total_sum: u128 = 0;
    for &amt in amounts.iter() {
        total_sum = safe_add(total_sum, amt)?;
    }
    if total_sum > 0 && total_sum < dust_limit {
        return Err(DistributionError::TotalBelowDustLimit);
    }

    // 1. Aggregate all allocations below dust.
    let sum_of_small_amounts: u128 = amounts.iter().filter(|&&amount| amount < dust_limit).sum();

    // 2. Remove sub-dust entries entirely.
    amounts.retain(|&amount| amount >= dust_limit);

    // 3. If nothing left after removal, decide whether to keep or discard.
    if amounts.is_empty() {
        if sum_of_small_amounts >= dust_limit {
            amounts.push(sum_of_small_amounts);
        } else {
            amounts.clear();
        }
        return Ok(());
    }

    // 4. Redistribute the collected dust across remaining outputs.
    let num_amounts = amounts.len() as u128;
    let to_add = safe_div(sum_of_small_amounts, num_amounts)?;
    let mut remainder = sum_of_small_amounts % num_amounts;

    for amount in amounts.iter_mut() {
        *amount = safe_add(*amount, to_add)?;
        if remainder > 0 {
            *amount = safe_add(*amount, 1)?;
            remainder -= 1;
        }
    }

    Ok(())
}

/// Calculates the total Rune token amount still owned by selected shards after
/// accounting for tokens that have already been removed.
///
/// This function performs a comprehensive audit of Rune holdings across all
/// selected shards, similar to [`compute_unsettled_btc_in_shards`] but for
/// Rune tokens. It aggregates all Rune amounts from each shard's `rune_utxo`
/// and subtracts any tokens specified in `removed_from_shards`.
///
/// # Type Parameters
/// * `RS` – Rune set type implementing [`FixedCapacitySet<Item = RuneAmount>`].
/// * `U` – UTXO info type implementing [`UtxoInfoTrait<RS>`].
/// * `S` – Shard type implementing [`StateShard<U, RS>`], [`ZeroCopy`], and [`Owner`].
///
/// # Parameters
/// * `selected_shards` – Slice of selected shards to audit for Rune holdings.
/// * `removed_from_shards` – Rune amounts already withdrawn from the shards
///   during the current instruction.
///
/// # Returns
/// A [`FixedCapacitySet`] containing the net Rune amounts that still need to be
/// redistributed back to the shards. Each [`RuneAmount`] in the set represents
/// a different Rune ID and its corresponding quantity.
///
/// # Errors
/// * [`StateShardError::RuneAmountAdditionOverflow`] – If aggregating Rune amounts
///   of the same ID exceeds the maximum value.
/// * [`StateShardError::RemovingMoreRunesThanPresentInShards`] – If
///   `removed_from_shards` contains more tokens of a specific ID than the shards
///   actually hold, indicating an inconsistent state.
///
/// # Implementation Details
/// * Iterates through each shard exactly once to gather all Rune holdings
/// * Uses `insert_or_modify` to aggregate amounts for Runes with identical IDs
/// * Performs safe subtraction to account for already-removed tokens
/// * Maintains type safety through the Rune set's fixed capacity constraints
#[cfg(feature = "runes")]
pub fn compute_unsettled_rune_in_shards<'info, RS, U, S>(
    selected_shards: &[Ref<'info, S>],
    removed_from_shards: RS,
) -> Result<RS, StateShardError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    let mut total_rune_amount = RS::default();

    for shard in selected_shards.iter() {
        // Traverse rune amounts directly without allocating an intermediate Vec.
        if let Some(utxo) = shard.rune_utxo() {
            for rune in utxo.runes().iter() {
                let _ = total_rune_amount.insert_or_modify::<StateShardError, _>(
                    RuneAmount {
                        id: rune.id,
                        amount: rune.amount,
                    },
                    |r| {
                        r.amount = safe_add(r.amount, rune.amount)
                            .map_err(|_| StateShardError::RuneAmountAdditionOverflow)?;
                        Ok(())
                    },
                );
            }
        };
    }

    // Subtract whatever was already removed.
    for rune in removed_from_shards.iter() {
        if let Some(output_rune) = total_rune_amount.find_mut(&rune.id) {
            output_rune.amount = safe_sub(output_rune.amount, rune.amount)
                .map_err(|_| StateShardError::RemovingMoreRunesThanPresentInShards)?;
        }
    }

    Ok(total_rune_amount)
}

/// Plans an optimal Rune token distribution across selected shards to achieve
/// balanced holdings without applying dust limits.
///
/// This function serves as the Rune equivalent of [`plan_btc_distribution_among_shards`],
/// using the same core balancing algorithm via [`balance_amount_across_shards`]
/// but without dust limit filtering since Runes don't have minimum value constraints
/// like Bitcoin UTXOs.
///
/// The function processes each Rune ID separately, computing an optimal allocation
/// for each token type across all selected shards and combining the results into
/// per-shard Rune sets.
///
/// # Type Parameters
/// * `MAX_MODIFIED_ACCOUNTS` – Maximum number of user-supplied UTXOs in the transaction.
/// * `MAX_INPUTS_TO_SIGN` – Maximum number of shards per program instance.
/// * `RS` – Rune set type implementing [`FixedCapacitySet<Item = RuneAmount>`].
/// * `U` – UTXO info type implementing [`UtxoInfoTrait<RS>`].
/// * `S` – Shard type implementing [`StateShard<U, RS>`], [`ZeroCopy`], and [`Owner`].
///
/// # Parameters
/// * `tx_builder` – Mutable reference to the transaction builder for context.
/// * `selected_shards` – Slice of selected shards to distribute tokens among.
/// * `amounts` – Rune set containing the token amounts to distribute across shards.
///
/// # Returns
/// A vector of Rune sets where each element corresponds to a selected shard and
/// contains the optimal allocation of tokens for that shard. The vector length
/// always equals `selected_shards.len()`.
///
/// # Errors
/// * [`StateShardError::MathErrorInBalanceAmountAcrossShards`] – If the underlying
///   balance calculation encounters arithmetic overflow or underflow.
/// * [`StateShardError::RuneAmountAdditionOverflow`] – If aggregating multiple
///   Rune allocations for the same ID exceeds numeric limits.
///
/// # Algorithm
/// 1. **Per-Rune processing**: Each Rune ID in `amounts` is processed separately
/// 2. **Balance calculation**: [`balance_amount_across_shards`] computes optimal
///    allocation for each Rune type
/// 3. **Result aggregation**: Allocations are combined into per-shard Rune sets
/// 4. **Zero filtering**: Shards with zero allocation for a Rune type are skipped
///
/// # Example
/// Given 2 shards and amounts `{RUNE_A: 1000, RUNE_B: 2000}`:
/// - RUNE_A gets distributed as `[500, 500]`
/// - RUNE_B gets distributed as `[1000, 1000]`  
/// - Result: `[{RUNE_A: 500, RUNE_B: 1000}, {RUNE_A: 500, RUNE_B: 1000}]`
#[cfg(feature = "runes")]
#[allow(clippy::too_many_arguments)]
pub fn plan_rune_distribution_among_shards<
    'info,
    const MAX_MODIFIED_ACCOUNTS: usize,
    const MAX_INPUTS_TO_SIGN: usize,
    RS,
    U,
    S,
>(
    tx_builder: &mut TransactionBuilder<MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN, RS>,
    selected_shards: &[Ref<'info, S>],
    amounts: &RS,
) -> Result<Vec<RS>, StateShardError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    let num_shards = selected_shards.len();
    let mut result: Vec<RS> = (0..num_shards).map(|_| RS::default()).collect();

    for rune_amount in amounts.iter() {
        let allocs = balance_amount_across_shards(tx_builder, selected_shards, rune_amount)
            .map_err(|_| StateShardError::MathErrorInBalanceAmountAcrossShards)?;

        for (i, amount) in allocs.iter().enumerate() {
            if *amount == 0 {
                continue;
            }
            result[i].insert_or_modify::<StateShardError, _>(
                RuneAmount {
                    id: rune_amount.id,
                    amount: *amount,
                },
                |r| {
                    r.amount = safe_add(r.amount, *amount)
                        .map_err(|_| StateShardError::RuneAmountAdditionOverflow)?;
                    Ok(())
                },
            )?;
        }
    }

    Ok(result)
}

/// Redistributes remaining Rune tokens across shards and generates corresponding
/// transaction outputs and runestone edicts for on-chain execution.
///
/// This function provides the complete Rune redistribution workflow, analogous to
/// [`redistribute_remaining_btc_to_shards`] but for Rune tokens. In addition to
/// planning the optimal distribution, it:
/// * **Creates transaction outputs**: Adds one output per participating shard,
///   each locked to `program_script_pubkey` with the minimum dust value.
/// * **Updates runestone pointer**: Sets the pointer to the first newly created
///   output so Runes are properly credited.
/// * **Generates edicts**: Creates [`Edict`] entries for all outputs except the
///   first (which receives Runes via the pointer mechanism).
///
/// # Type Parameters
/// * `MAX_MODIFIED_ACCOUNTS` – Maximum number of user-supplied UTXOs in the transaction.
/// * `MAX_INPUTS_TO_SIGN` – Maximum number of shards per program instance.
/// * `RS` – Rune set type implementing [`FixedCapacitySet<Item = RuneAmount>`].
/// * `U` – UTXO info type implementing [`UtxoInfoTrait<RS>`].
/// * `S` – Shard type implementing [`StateShard<U, RS>`], [`ZeroCopy`], and [`Owner`].
///
/// # Parameters
/// * `tx_builder` – Mutable reference to the transaction builder. The embedded
///   runestone will be modified to include the necessary pointer and edicts.
/// * `selected_shards` – Slice of selected shards to redistribute tokens among.
/// * `removed_from_shards` – Rune amounts already withdrawn from the shards,
///   used to calculate remaining amounts via [`compute_unsettled_rune_in_shards`].
/// * `program_script_pubkey` – Script that will lock all newly created outputs
///   back to the program.
///
/// # Returns
/// A vector of Rune sets representing the final distribution, sorted in descending
/// order by total Rune amount per shard. Each element corresponds to one created
/// output and contains all Rune allocations for that output.
///
/// # Errors
/// * [`StateShardError`] variants from underlying computation functions:
///   * `RuneAmountAdditionOverflow` – If Rune amount calculations overflow
///   * `RemovingMoreRunesThanPresentInShards` – If `removed_from_shards` exceeds holdings
///   * `MathErrorInBalanceAmountAcrossShards` – If distribution planning fails
///
/// # Runestone Protocol Details
/// * **Pointer mechanism**: The first output receives Runes automatically via the
///   runestone pointer, requiring no explicit edict.
/// * **Edict generation**: Subsequent outputs require explicit [`Edict`] entries
///   specifying the Rune ID, amount, and destination output index.
/// * **Output ordering**: Results are sorted by total Rune value for deterministic
///   behavior, similar to the BTC redistribution function.
///
/// # Example
/// For 2 shards with `{RUNE_A: 1000}` to redistribute:
/// 1. Creates 2 outputs at indices N and N+1
/// 2. Sets `runestone.pointer = Some(N)`
/// 3. Adds edict: `{id: RUNE_A, amount: 500, output: N+1}`
/// 4. First output (N) gets 500 RUNE_A via pointer
/// 5. Second output (N+1) gets 500 RUNE_A via edict
#[cfg(feature = "runes")]
#[allow(clippy::too_many_arguments)]
pub fn redistribute_remaining_rune_to_shards<
    'info,
    const MAX_MODIFIED_ACCOUNTS: usize,
    const MAX_INPUTS_TO_SIGN: usize,
    RS,
    U,
    S,
>(
    tx_builder: &mut TransactionBuilder<MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN, RS>,
    selected_shards: &[Ref<'info, S>],
    removed_from_shards: RS,
    program_script_pubkey: ScriptBuf,
) -> Result<Vec<RS>, StateShardError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    let remaining_amount = compute_unsettled_rune_in_shards(selected_shards, removed_from_shards)?;

    let mut distribution =
        plan_rune_distribution_among_shards(tx_builder, selected_shards, &remaining_amount)?;

    // Sort descending by total rune amount for deterministic ordering.
    distribution.sort_by(|a, b| {
        let total_a: u128 = a.iter().map(|r| r.amount).sum();
        let total_b: u128 = b.iter().map(|r| r.amount).sum();
        total_b.cmp(&total_a)
    });

    let current_output_index = tx_builder.transaction.output.len();
    tx_builder.runestone.pointer = Some(current_output_index as u32);

    let mut index = current_output_index;
    for amount_set in distribution.iter() {
        tx_builder.transaction.output.push(TxOut {
            value: Amount::from_sat(DUST_LIMIT),
            script_pubkey: program_script_pubkey.clone(),
        });

        if index > current_output_index {
            for rune_amount in amount_set.iter() {
                tx_builder.runestone.edicts.push(Edict {
                    id: ordinals::RuneId {
                        block: rune_amount.id.block,
                        tx: rune_amount.id.tx,
                    },
                    amount: rune_amount.amount,
                    output: index as u32,
                });
            }
        }

        index += 1;
    }

    Ok(distribution)
}

#[cfg(test)]
mod tests_loader {
    use super::super::tests::common::{
        create_btc_utxo, create_shard, leak_loaders_from_vec, MockShardZc,
    };
    use super::*;
    // use crate::shard_set::ShardSet;
    use satellite_bitcoin::utxo_info::SingleRuneSet;
    use satellite_lang::prelude::AccountLoader;
    use std::cell::Ref;

    // Re-export for macro reuse
    use satellite_bitcoin::TransactionBuilder as TB;

    #[allow(unused_macros)]
    macro_rules! new_tb {
        ($max_modified_accounts:expr, $max_inputs_to_sign:expr) => {
            TB::<$max_modified_accounts, $max_inputs_to_sign, SingleRuneSet>::new()
        };
    }

    /// Helper function to create Ref instances directly from loaders for selected indices
    pub fn create_shard_refs_from_loaders<'info>(
        loaders: &'info [AccountLoader<'info, MockShardZc>],
        indices: &[usize],
    ) -> Result<Vec<Ref<'info, MockShardZc>>, arch_program::program_error::ProgramError> {
        let mut refs = Vec::new();
        for &idx in indices {
            refs.push(loaders[idx].load()?);
        }
        Ok(refs)
    }

    mod plan_btc_distribution_among_shards {
        use super::super::super::split;

        use super::*;
        use satellite_bitcoin::{constants::DUST_LIMIT, utxo_info::SingleRuneSet};
        use split::plan_btc_distribution_among_shards;

        #[test]
        fn proportional_distribution_insufficient_remaining() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 3;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // Shards with 100,200,300 sats respectively
            let shards: Vec<MockShardZc> =
                vec![create_shard(100), create_shard(200), create_shard(300)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

            // Remaining amount smaller than dust → expect empty dist
            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 150u128);
            assert!(matches!(dist, Err(DistributionError::TotalBelowDustLimit)));
        }

        #[test]
        fn zero_remaining_amount() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(1_000), create_shard(2_000)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 0u128)
            .unwrap();
            assert!(dist.is_empty());
        }

        #[test]
        fn single_shard() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 1;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(500)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 1_000u128)
            .unwrap();

            assert_eq!(dist, vec![1_000]);
        }

        #[test]
        fn empty_shards_all_zero_balances() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 3;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0), create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 1_500u128)
            .unwrap();

            assert_eq!(dist, vec![1_500]);
        }

        #[test]
        fn remainder_distribution_sub_dust_merge() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 3;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0), create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

            let amount = 1_001u128;
            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, amount)
            .unwrap();
            assert_eq!(dist.iter().sum::<u128>(), amount);
            assert_eq!(dist, vec![amount]);
        }

        #[test]
        fn used_utxos_excluded() {
            use bitcoin::{transaction::Version, OutPoint, ScriptBuf, Sequence, TxIn, Witness};

            const MAX_MODIFIED_ACCOUNTS: usize = 1;
            const MAX_INPUTS_TO_SIGN: usize = 2;

            let mut tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // Shards with 1_000 sats each
            let shard1 = create_shard(1_000);
            let shard2 = create_shard(1_000);

            // Capture meta before loader creation via trait method
            let used_meta = shard1.btc_utxos()[0].meta;

            let loaders = leak_loaders_from_vec(vec![shard1, shard2]);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            // Mark first shard's utxo as spent
            tx_builder.transaction.version = Version::TWO;
            tx_builder.transaction.input.push(TxIn {
                previous_output: OutPoint::new(used_meta.to_txid(), used_meta.vout()),
                script_sig: ScriptBuf::new(),
                sequence: Sequence::MAX,
                witness: Witness::new(),
            });

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 1_000u128)
            .unwrap();

            assert_eq!(dist, vec![1_000]);
        }

        #[test]
        fn partial_shard_selection() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 4;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![
                create_shard(1_000),
                create_shard(2_000),
                create_shard(3_000),
                create_shard(4_000),
            ];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[1, 2]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 2_000u128)
            .unwrap();

            assert_eq!(dist.iter().sum::<u128>(), 2_000);
            assert_eq!(dist, vec![2_000]);
        }

        #[test]
        fn large_numbers() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(u64::MAX), create_shard(u64::MAX)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 1_000u128)
            .unwrap();

            assert_eq!(dist, vec![1_000]);
        }

        #[test]
        fn split_remaining_amount_even_and_odd() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            // Odd amount
            let dist_odd = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 2_041u128)
            .unwrap();
            assert_eq!(dist_odd, vec![1_021, 1_020]);
            assert_eq!(dist_odd.iter().sum::<u128>(), 2_041);

            // Even amount
            let dist_even = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 2_000u128)
            .unwrap();
            assert_eq!(dist_even, vec![1_000, 1_000]);
        }

        #[test]
        fn split_remaining_amount_with_existing_balances() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(1_000), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 2_041u128)
            .unwrap();

            assert_eq!(dist.iter().sum::<u128>(), 2_041);
            assert_eq!(dist, vec![2_041]);
        }

        #[test]
        fn single_shard_sub_dust_amount() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 1;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, (DUST_LIMIT as u128) - 1u128);
            assert!(matches!(dist, Err(DistributionError::TotalBelowDustLimit)));
        }

        #[test]
        fn single_shard_exact_dust_limit() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 1;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, DUST_LIMIT as u128)
            .unwrap();

            assert_eq!(dist, vec![DUST_LIMIT as u128]);
        }

        #[test]
        fn two_shards_each_exact_dust_limit() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            let amount = (DUST_LIMIT as u128) * 2u128;
            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, amount)
            .unwrap();

            assert_eq!(dist, vec![DUST_LIMIT as u128, DUST_LIMIT as u128]);
        }

        #[test]
        fn mixed_dust_and_non_dust_allocations() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 3;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0), create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

            let amount = 1_600u128; // provisional 533/533/534 (< dust)
            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, amount)
            .unwrap();

            assert_eq!(dist, vec![amount]);
        }
    }

    // ---------------------------------------------------------------
    // compute_unsettled_btc_in_shards --------------------------------
    // ---------------------------------------------------------------
    mod compute_unsettled_btc_in_shards {
        use super::super::compute_unsettled_btc_in_shards;
        use super::*;
        use bitcoin::{OutPoint, ScriptBuf, Sequence, TxIn, Witness};
        use satellite_bitcoin::fee_rate::FeeRate;

        #[test]
        fn basic_unsettled_calculation() {
            const MAX_MODIFIED_ACCOUNTS: usize = 2;
            const MAX_INPUTS_TO_SIGN: usize = 2;

            let mut tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // Two shards with 1_000 and 500 sats respectively
            let shard1 = create_shard(1_000);
            let shard2 = create_shard(500);

            // Capture meta before moving shards into loaders
            let spent_meta = shard1.btc_utxos()[0].meta;

            let loaders = leak_loaders_from_vec(vec![shard1, shard2]);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            // Spend shard 0's UTXO in the transaction
            tx_builder.transaction.input.push(TxIn {
                previous_output: OutPoint::new(spent_meta.to_txid(), spent_meta.vout()),
                script_sig: ScriptBuf::new(),
                sequence: Sequence::MAX,
                witness: Witness::new(),
            });

            let unsettled = compute_unsettled_btc_in_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 1_000, &FeeRate(1.0))
            .unwrap();

            // Only shard 0's 1000 sats are unsettled (shard 1 untouched)
            assert_eq!(unsettled, 500);
        }
    }

    // ---------------------------------------------------------------
    // Edge-case helpers & stress tests --------------------------------
    // ---------------------------------------------------------------
    mod edge_cases {
        use super::super::super::tests::common::add_btc_utxos_bulk;
        use super::super::super::tests::common::random_utxo_meta;
        use super::super::{
            balance_amount_across_shards as balance_loader, compute_unsettled_btc_in_shards,
            plan_btc_distribution_among_shards, redistribute_sub_dust_values,
        };
        use super::*;
        use bitcoin::{OutPoint, ScriptBuf, Sequence, TxIn, Witness};
        use satellite_bitcoin::MathError;
        use satellite_bitcoin::{constants::DUST_LIMIT, fee_rate::FeeRate};
        use satellite_lang::prelude::AccountLoader;

        // ---- redistribute_sub_dust_values tests ----
        #[test]
        fn redistribute_sub_dust_all_above_dust() {
            let mut amounts = vec![1000u128, 2000u128, 3000u128];
            let original = amounts.clone();
            redistribute_sub_dust_values(&mut amounts, DUST_LIMIT as u128).unwrap();
            assert_eq!(amounts, original);
        }

        #[test]
        fn redistribute_sub_dust_all_below_but_sum_above() {
            let mut amounts = vec![200u128, 200u128, 200u128];
            redistribute_sub_dust_values(&mut amounts, DUST_LIMIT as u128).unwrap();
            assert_eq!(amounts, vec![600u128]);
        }

        #[test]
        fn redistribute_sub_dust_mixed_with_remainder() {
            let mut amounts = vec![1000u128, 200u128, 300u128, 2000u128]; // 200+300 below dust
            redistribute_sub_dust_values(&mut amounts, DUST_LIMIT as u128).unwrap();
            assert_eq!(amounts.len(), 2);
            assert_eq!(amounts.iter().sum::<u128>(), 3500u128);
            assert!(amounts.contains(&1250u128));
            assert!(amounts.contains(&2250u128));
        }

        #[test]
        fn redistribute_sub_dust_total_below_dust_returns_error() {
            let mut amounts = vec![200u128, 300u128]; // total 500 < dust
            let res = redistribute_sub_dust_values(&mut amounts, DUST_LIMIT as u128);
            assert!(matches!(
                res,
                Err(super::super::DistributionError::TotalBelowDustLimit)
            ));
        }

        // ---- zero-shard behaviour ----
        #[test]
        fn plan_btc_distribution_zero_shards() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 0;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // Empty loaders slice
            let loaders: &[AccountLoader<'static, MockShardZc>] = &[];
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[]).unwrap();

            let result = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 1_000u128);

            assert!(matches!(
                result,
                Err(DistributionError::Math(MathError::DivisionOverflow))
            ));
        }

        // ---- max-capacity stress ----
        #[test]
        fn max_capacity_stress() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 10;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // Build 10 shards, each with 5 × 1_000-sat UTXOs
            let shards: Vec<MockShardZc> = (0..MAX_INPUTS_TO_SIGN)
                .map(|i| {
                    let mut s = create_shard(0);
                    let values = vec![1_000u64; 5];
                    add_btc_utxos_bulk(&mut s, &values);
                    // tweak vout base by index to make metas unique
                    if i > 0 {
                        // Already sequential in helper but fine
                    }
                    s
                })
                .collect();

            let loaders = leak_loaders_from_vec(shards);
            let shard_refs =
                create_shard_refs_from_loaders(&loaders, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]).unwrap();

            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 10_000u128)
            .unwrap();

            assert_eq!(dist.iter().sum::<u128>(), 10_000u128);
        }

        // ---- near-boundary dust split cases ----
        #[test]
        fn near_boundary_dust_splits_below() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 3;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0), create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

            let amount = (DUST_LIMIT as u128) * 3 - 1u128;
            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, amount)
            .unwrap();

            assert!(dist.len() < 3);
            assert_eq!(dist.iter().sum::<u128>(), amount);
        }

        #[test]
        fn near_boundary_dust_splits_above() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 3;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shards = vec![create_shard(0), create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let shard_refs = create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

            let amount = (DUST_LIMIT as u128) * 3 + 1u128;
            let dist = plan_btc_distribution_among_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, amount)
            .unwrap();

            assert_eq!(dist.len(), 3);
            assert!(dist.iter().all(|&x| x >= DUST_LIMIT as u128));
            assert_eq!(dist.iter().sum::<u128>(), amount);
        }

        // ---- duplicate meta across shards ----
        #[test]
        fn duplicate_meta_utxos_across_shards() {
            const MAX_MODIFIED_ACCOUNTS: usize = 1;
            const MAX_INPUTS_TO_SIGN: usize = 2;

            let mut tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // Build two UTXOs with IDENTICAL meta but different values
            let shared_meta = random_utxo_meta(42);
            let utxo1 = create_btc_utxo(1_000, 42);
            let mut utxo2 = create_btc_utxo(2_000, 42); // same meta
            utxo2.meta = shared_meta; // ensure identical even if helper differs

            let mut shard1 = create_shard(0);
            let mut shard2 = create_shard(0);
            shard1.add_btc_utxo(utxo1);
            shard2.add_btc_utxo(utxo2);

            let loaders = leak_loaders_from_vec(vec![shard1, shard2]);
            // Load shard references directly (indices 0 and 1)
            let shard_refs = super::create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            // Spend the shared UTXO in the tx
            tx_builder.transaction.input.push(TxIn {
                previous_output: OutPoint::new(shared_meta.to_txid(), shared_meta.vout()),
                script_sig: ScriptBuf::new(),
                sequence: Sequence::MAX,
                witness: Witness::new(),
            });

            let unsettled = compute_unsettled_btc_in_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, 0, &FeeRate(1.0))
            .unwrap();

            assert_eq!(unsettled, 3_000);
        }

        // ---- high fee overflow handling ----
        #[test]
        fn high_fee_scenario_overflow() {
            use arch_program::rune::{RuneAmount, RuneId};
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 1;

            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            let shard = create_shard(0);
            let loaders = leak_loaders_from_vec(vec![shard]);
            let shard_refs = super::create_shard_refs_from_loaders(&loaders, &[0]).unwrap();

            // Add a huge rune amount -> expect overflow handled gracefully (Err)
            let rune_amount = RuneAmount {
                id: RuneId::BTC,
                amount: u128::MAX,
            };
            let result = balance_loader::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, &rune_amount);

            // Should succeed and return the full allocation for the single shard.
            assert_eq!(result.unwrap(), vec![u128::MAX]);
        }

        // ---- empty amount optimisation ----
        #[test]
        fn empty_amount_optimization() {
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;

            let mut tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // preload some outputs
            let original_outputs = tx_builder.transaction.output.len();

            let shards = vec![create_shard(1_000), create_shard(2_000)];
            let loaders = leak_loaders_from_vec(shards);
            let mut shard_refs = super::create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            let dist = super::super::redistribute_remaining_btc_to_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut tx_builder,
                &mut shard_refs,
                0,
                &ScriptBuf::new(),
                &FeeRate(1.0),
            )
            .unwrap();

            assert!(dist.is_empty());
            assert_eq!(tx_builder.transaction.output.len(), original_outputs);
        }

        // ---- overflow protection in balance_amount_across_shards ----
        #[test]
        fn balance_amount_overflow_protection() {
            use arch_program::rune::{RuneAmount, RuneId};
            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;
            let tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // shards with u64::MAX utxos
            let mut shard1 = create_shard(0);
            let mut shard2 = create_shard(0);
            shard1.add_btc_utxo(create_btc_utxo(u64::MAX, 1));
            shard2.add_btc_utxo(create_btc_utxo(u64::MAX, 2));

            let loaders = leak_loaders_from_vec(vec![shard1, shard2]);
            let shard_refs = super::create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            let rune_amount = RuneAmount {
                id: RuneId::BTC,
                amount: u128::MAX,
            };
            let res = balance_loader::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&tx_builder, &shard_refs, &rune_amount);

            assert!(res.is_err());
        }

        // ---- runestone pointer update (Rune feature) ----
        #[cfg(feature = "runes")]
        #[test]
        fn runestone_pointer_update() {
            use bitcoin::{Amount, TxOut};

            const MAX_MODIFIED_ACCOUNTS: usize = 0;
            const MAX_INPUTS_TO_SIGN: usize = 2;

            let mut tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

            // Pre-existing outputs to simulate prior transaction state.
            tx_builder.transaction.output.push(TxOut {
                value: Amount::from_sat(1_000),
                script_pubkey: ScriptBuf::new(),
            });
            tx_builder.transaction.output.push(TxOut {
                value: Amount::from_sat(2_000),
                script_pubkey: ScriptBuf::new(),
            });

            let old_output_count = tx_builder.transaction.output.len();

            // Two empty shards (no BTC / Rune UTXOs needed for this test)
            let shards = vec![create_shard(0), create_shard(0)];
            let loaders = leak_loaders_from_vec(shards);
            let mut shard_refs = super::create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

            // Invoke the rune redistribution helper (no runes to distribute)
            crate::split::redistribute_remaining_rune_to_shards::<
                MAX_MODIFIED_ACCOUNTS,
                MAX_INPUTS_TO_SIGN,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut tx_builder,
                &mut shard_refs,
                SingleRuneSet::default(),
                ScriptBuf::new(),
            )
            .unwrap();

            // Pointer should now reference the first newly added output.
            assert_eq!(tx_builder.runestone.pointer, Some(old_output_count as u32));

            // Any generated edicts (if present) must point to subsequent outputs.
            for (i, edict) in tx_builder.runestone.edicts.iter().enumerate() {
                if i > 0 {
                    assert_eq!(edict.output, (old_output_count + i) as u32);
                }
            }
        }
    }
}

// -------------------------------------------------------------------------
// Rune-specific test suite (requires `--features runes`)
// -------------------------------------------------------------------------
#[cfg(all(test, feature = "runes"))]
mod rune_tests_loader {
    use super::*;
    // use crate::shard_set::ShardSet;
    use crate::tests::common::{
        create_rune_utxo, create_shard, leak_loaders_from_vec, MockShardZc,
    };
    use arch_program::rune::{RuneAmount, RuneId};
    use bitcoin::ScriptBuf;
    use satellite_bitcoin::utxo_info::SingleRuneSet;
    use satellite_bitcoin::TransactionBuilder as TB;

    #[allow(unused_macros)]
    macro_rules! new_tb {
        ($max_utxos:expr, $max_shards:expr) => {
            TB::<$max_utxos, $max_shards, SingleRuneSet>::new()
        };
    }

    // ---------------------------------------------------------------
    // compute_unsettled_rune_in_shards ------------------------------
    // ---------------------------------------------------------------
    #[test]
    fn compute_unsettled_rune_basic() {
        const MAX_MODIFIED_ACCOUNTS: usize = 0;
        const MAX_INPUTS_TO_SIGN: usize = 2;

        // Two shards with 100 and 50 runes respectively
        let mut shard1 = create_shard(0);
        let mut shard2 = create_shard(0);
        shard1.set_rune_utxo(create_rune_utxo(100, 0));
        shard2.set_rune_utxo(create_rune_utxo(50, 1));

        let loaders = leak_loaders_from_vec(vec![shard1, shard2]);
        let shard_refs =
            super::tests_loader::create_shard_refs_from_loaders(&loaders, &[0, 1]).unwrap();

        let unsettled = crate::split::compute_unsettled_rune_in_shards::<
            SingleRuneSet,
            satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
            MockShardZc,
        >(&shard_refs, SingleRuneSet::default())
        .unwrap();

        assert_eq!(unsettled.find(&RuneId::new(1, 1)).unwrap().amount, 150);
    }

    // ---------------------------------------------------------------
    // plan_rune_distribution_among_shards ---------------------------
    // ---------------------------------------------------------------
    #[test]
    fn plan_rune_distribution_proportional() {
        const MAX_MODIFIED_ACCOUNTS: usize = 0;
        const MAX_INPUTS_TO_SIGN: usize = 3;

        let mut tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

        // Existing rune balances: 100, 200, 300
        let mut shard0 = create_shard(0);
        let mut shard1 = create_shard(0);
        let mut shard2 = create_shard(0);
        shard0.set_rune_utxo(create_rune_utxo(100, 0));
        shard1.set_rune_utxo(create_rune_utxo(200, 1));
        shard2.set_rune_utxo(create_rune_utxo(300, 2));

        let loaders = leak_loaders_from_vec(vec![shard0, shard1, shard2]);
        let shard_refs =
            super::tests_loader::create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

        // Distribute 600 runes proportionally
        let mut target = SingleRuneSet::default();
        target
            .insert(RuneAmount {
                id: RuneId::new(1, 1),
                amount: 600,
            })
            .unwrap();

        let dist = crate::split::plan_rune_distribution_among_shards::<
            MAX_MODIFIED_ACCOUNTS,
            MAX_INPUTS_TO_SIGN,
            SingleRuneSet,
            satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
            MockShardZc,
        >(&mut tx_builder, &shard_refs, &target)
        .unwrap();

        assert_eq!(dist.len(), 3);
        let allocs: Vec<u128> = dist
            .iter()
            .map(|s| s.find(&RuneId::new(1, 1)).unwrap().amount)
            .collect();
        assert_eq!(allocs, vec![300, 200, 100]);
    }

    // ---------------------------------------------------------------
    // redistribute_remaining_rune_to_shards -------------------------
    // ---------------------------------------------------------------
    #[test]
    fn redistribute_remaining_rune_distribution() {
        const MAX_MODIFIED_ACCOUNTS: usize = 0;
        const MAX_INPUTS_TO_SIGN: usize = 3;

        let mut tx_builder = new_tb!(MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN);

        // Shards start with 100, 200, 300 runes
        let mut shard0 = create_shard(0);
        let mut shard1 = create_shard(0);
        let mut shard2 = create_shard(0);
        shard0.set_rune_utxo(create_rune_utxo(100, 0));
        shard1.set_rune_utxo(create_rune_utxo(200, 1));
        shard2.set_rune_utxo(create_rune_utxo(300, 2));

        let loaders = leak_loaders_from_vec(vec![shard0, shard1, shard2]);
        let mut shard_refs =
            super::tests_loader::create_shard_refs_from_loaders(&loaders, &[0, 1, 2]).unwrap();

        // Remove 150 runes total
        let mut removed = SingleRuneSet::default();
        removed
            .insert(RuneAmount {
                id: RuneId::new(1, 1),
                amount: 150,
            })
            .unwrap();

        let dist = crate::split::redistribute_remaining_rune_to_shards::<
            MAX_MODIFIED_ACCOUNTS,
            MAX_INPUTS_TO_SIGN,
            SingleRuneSet,
            satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
            MockShardZc,
        >(&mut tx_builder, &mut shard_refs, removed, ScriptBuf::new())
        .unwrap();

        // Expect proportional (75, 150, 225) regardless of ordering
        let mut allocs: Vec<u128> = dist
            .iter()
            .map(|s| s.find(&RuneId::new(1, 1)).unwrap().amount)
            .collect();
        allocs.sort_unstable();
        assert_eq!(allocs, vec![50, 150, 250]);
    }
}
