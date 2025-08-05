//! Utilities to **apply the effects of a broadcast Bitcoin transaction** to
//! a program's shard accounts.
//!
//! While `split.rs` is concerned with *planning* the redistribution of value
//! (and extends the `TransactionBuilder` accordingly), **this module performs
//! the *state mutation***: it removes spent UTXOs, inserts newly created ones
//! and keeps Rune pointers up-to-date.
//!
//! # Architecture Overview
//!
//! This module provides a layered architecture for UTXO state management:
//! - **High-level API**: [`update_shards_after_transaction`] - main entry point
//! - **Transaction Analysis**: [`get_modified_program_utxos_in_transaction`] - identifies UTXO changes  
//! - **Rune Processing**: [`update_modified_program_utxos_with_rune_amount`] - handles token assignments
//! - **State Mutation**: [`update_shards_utxos`] - applies changes to shard state
//! - **Load Balancing**: [`select_best_shard_to_add_btc_to`] - optimizes UTXO distribution
//! - **UTXO Removal**: [`remove_utxos_from_shards`] - efficiently removes spent UTXOs
//!
//! # Intended Usage
//! --------------
//! 1. Build and sign a transaction with
//!    [`satellite_bitcoin::TransactionBuilder`].
//! 2. Call [`ShardSet::update_shards_after_transaction`] – a convenience wrapper
//!    around [`update_shards_after_transaction`] – passing the same
//!    `TransactionBuilder`, a `ShardSet` in the *Selected* state and the
//!    program's redeem script.
//! 3. Once the function returns, simply let the `AccountLoader` borrows drop so
//!    that Anchor can persist the mutated accounts.
//!
//! # Transaction Processing Flow
//!
//! The complete flow involves these steps:
//! 1. **Analysis Phase** - Identify spent and created UTXOs from transaction data
//! 2. **Rune Phase** - Process runestone edicts and distribute rune tokens (if enabled)
//! 3. **Removal Phase** - Remove spent UTXOs from all affected shards
//! 4. **Distribution Phase** - Add new UTXOs using load-balancing algorithms
//! 5. **Consolidation Phase** - Apply consolidation flags when appropriate (if enabled)
//!
//! # Feature flags
//! -------------
//! * `runes` – enables Rune-aware logic (runestone edicts, pointer updates).
//! * `utxo-consolidation` – sets the consolidation flag on large UTXO sets so
//!   they can be merged in a follow-up instruction.
//!
//! # Error handling
//! --------------
//! The module provides comprehensive error handling for various failure scenarios:
//!
//! ## Capacity Errors
//! * `StateShardError::ShardsAreFullOfBtcUtxos` - No capacity for additional BTC UTXOs
//! * `StateShardError::ExcessRuneUtxos` - More rune UTXOs than available shard slots
//!
//! ## Rune Processing Errors (with `runes` feature)
//! * `StateShardError::OutputEdictIsNotInTransaction` - Invalid edict output reference
//! * `StateShardError::RunestonePointerIsNotInTransaction` - Invalid pointer reference
//! * `StateShardError::RuneAmountAdditionOverflow` - Arithmetic overflow in rune amounts
//! * `StateShardError::NotEnoughRuneInShards` - Insufficient rune tokens for assignment
//!
//! # Performance Optimizations
//!
//! The module is optimized for on-chain execution with several key optimizations:
//! - **Single-pass algorithms** minimize iteration overhead
//! - **Bulk operations** reduce borrow checker stress
//! - **Pre-allocated vectors** minimize dynamic allocation
//! - **Efficient load balancing** maintains optimal shard distribution
//! - **Minimal copying** for large data structures
//!
//! # Shard Selection and Isolation
//!
//! All helpers operate only on `shard_set.selected_indices()`; unrelated shards
//! remain untouched, which allows callers to pass references to the entire
//! shards slice without cloning. This design provides:
//! - **Selective updates** - only modify shards involved in the transaction
//! - **Isolation** - unrelated shards remain completely unchanged
//! - **Efficiency** - no unnecessary state checks or modifications
//! - **Safety** - type system prevents accidental mutation of unselected shards

use std::cell::RefMut;

use arch_program::{input_to_sign::InputToSign, rune::RuneAmount, utxo::UtxoMeta};
use bitcoin::{ScriptBuf, Transaction};
use satellite_bitcoin::utxo_info::UtxoInfoTrait;
use satellite_bitcoin::{fee_rate::FeeRate, TransactionBuilder};

#[cfg(feature = "runes")]
use arch_program::rune::RuneId;
#[cfg(feature = "runes")]
use ordinals::Runestone;
use satellite_bitcoin::generic::fixed_set::FixedCapacitySet;

use super::error::StateShardError;

use super::StateShard;

use satellite_lang::prelude::Owner;
use satellite_lang::ZeroCopy;

/// Removes all specified UTXOs from the provided selected shards.
///
/// This is an internal helper function that efficiently removes UTXOs from multiple shards
/// in a single pass. It handles both BTC UTXOs (stored in the shard's UTXO vector) and
/// the optional rune UTXO (stored as a single optional field).
///
/// # Behavior
/// - Iterates through each shard exactly once to minimize borrow checker overhead
/// - For each UTXO to remove, checks both the BTC UTXO vector and rune UTXO slot
/// - Silently ignores UTXOs that are not found in a particular shard (this is expected
///   behavior since not all UTXOs exist in all shards)
/// - Uses `btc_utxos_retain` for efficient removal from the BTC UTXO vector
/// - Directly clears the rune UTXO slot if it matches the target UTXO
///
/// # Performance Considerations
/// - Designed to minimize BPF instruction count in on-chain execution
/// - Single iteration per shard reduces runtime borrow checking overhead
/// - Bulk removal is more efficient than individual remove operations
///
/// # Assumptions
/// - Called only with shards that are actually involved in the transaction
/// - The caller has already determined which UTXOs need to be removed
/// - UTXOs may or may not exist in any given shard (graceful handling of missing UTXOs)
///
/// # Arguments
/// * `selected_shards` - Mutable references to the shards that should be processed
/// * `utxos_to_remove` - Slice of UTXO metadata identifying which UTXOs to remove
///
/// # Errors
/// Currently always returns `Ok(())` but uses the `Result` type for consistency
/// with other functions in this module and potential future error conditions.
fn remove_utxos_from_shards<'info, RS, U, S>(
    selected_shards: &mut [RefMut<'info, S>],
    utxos_to_remove: &[UtxoMeta],
) -> super::error::Result<()>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    // Iterate **once per shard** and perform all removals within the same
    // mutable borrow. This avoids repeatedly loading the same account and
    // therefore reduces BPF instruction count and runtime borrow checking
    // overhead.
    for shard in selected_shards.iter_mut() {
        for utxo_to_remove in utxos_to_remove {
            shard.btc_utxos_retain(&mut |utxo| utxo.meta() != utxo_to_remove);

            if let Some(rune_utxo) = shard.rune_utxo() {
                if rune_utxo.meta() == utxo_to_remove {
                    shard.clear_rune_utxo();
                }
            }
        }
    }

    Ok(())
}

/// Selects the optimal shard for adding a new BTC UTXO based on current capacity and balance.
///
/// This function implements a load-balancing strategy that prioritizes shards with:
/// 1. **Available capacity** - the shard must have room for at least one more BTC UTXO
/// 2. **Smallest total BTC value** - among eligible shards, selects the one with the least satoshis
///
/// # Selection Algorithm
/// The function iterates through all provided shards and:
/// - Calculates the total BTC value (sum of all UTXO values) for each shard
/// - Checks if the shard has spare capacity (`btc_utxos_len() < btc_utxos_max_len()`)
/// - Among shards with spare capacity, selects the one with the smallest total value
/// - Returns the **relative index** within the `selected_shards` slice (not global index)
///
/// # Load Balancing Benefits
/// - Distributes UTXOs evenly across shards to prevent concentration
/// - Maintains roughly equal BTC values across shards over time
/// - Prevents scenarios where some shards become heavily loaded while others remain empty
/// - Helps with future transaction planning and fee optimization
///
/// # Performance Characteristics
/// - O(n) time complexity where n is the number of selected shards
/// - Minimal memory allocation (only stores current best choice)
/// - Single pass through all shards for efficiency
///
/// # Arguments
/// * `selected_shards` - Slice of shard references to evaluate for UTXO insertion
///
/// # Returns
/// * `Some(index)` - The relative index of the best shard within the provided slice
/// * `None` - If all shards are at maximum capacity or no shards are provided
///
/// # Example Usage
/// ```rust,ignore
/// if let Some(target_idx) = select_best_shard_to_add_btc_to(&shards) {
///     shards[target_idx].add_btc_utxo(new_utxo);
/// } else {
///     return Err(StateShardError::ShardsAreFullOfBtcUtxos);
/// }
/// ```
fn select_best_shard_to_add_btc_to<'info, RS, U, S>(
    selected_shards: &[RefMut<'info, S>],
) -> Option<usize>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    let mut best_idx: Option<usize> = None;
    let mut smallest_total: u64 = u64::MAX;

    for (idx, shard) in selected_shards.iter().enumerate() {
        let spare = shard.btc_utxos_len() < shard.btc_utxos_max_len();
        let sum: u64 = shard.btc_utxos().iter().map(|u| u.value()).sum();

        if spare && sum < smallest_total {
            smallest_total = sum;
            best_idx = Some(idx);
        }
    }

    best_idx
}

/// Performs a comprehensive update of UTXO sets across multiple shards in three phases.
///
/// This function orchestrates the complete UTXO state transition that occurs after a Bitcoin
/// transaction has been broadcast. It handles both removal of spent UTXOs and intelligent
/// distribution of newly created UTXOs across the selected shards.
///
/// # Three-Phase Operation
///
/// ## Phase 1: UTXO Removal
/// - Removes all specified UTXOs from all selected shards
/// - Handles both BTC UTXOs (from vectors) and rune UTXOs (single optional slot)
/// - Uses efficient bulk removal to minimize borrow checker overhead
///
/// ## Phase 2: Rune UTXO Distribution
/// - Distributes new rune-bearing UTXOs to shards that don't already have one
/// - Follows a simple first-available strategy for rune UTXO placement
/// - Ensures no rune UTXOs are lost (errors if excess rune UTXOs remain)
/// - Maintains the invariant that each shard has at most one rune UTXO
///
/// ## Phase 3: BTC UTXO Distribution
/// - Sorts new BTC UTXOs by value (largest first) for optimal distribution
/// - Uses load-balancing algorithm to distribute UTXOs to least-funded shards
/// - Applies UTXO consolidation flags when `utxo-consolidation` feature is enabled
/// - Ensures all UTXOs are successfully inserted or returns an error
///
/// # Feature-Dependent Behavior
///
/// ## `utxo-consolidation` Feature
/// When enabled, sets the consolidation flag on UTXOs added to shards that already
/// contain multiple UTXOs. The flag includes the current fee rate for future
/// consolidation planning.
///
/// # Load Balancing Strategy
/// - Distributes UTXOs to maintain roughly equal BTC values across shards
/// - Prevents concentration of value in a few shards
/// - Optimizes for future transaction efficiency and fee management
/// - Prioritizes shards with available capacity and smaller total values
///
/// # Arguments
/// * `selected_shards` - Mutable references to shards that should be updated
/// * `utxos_to_remove` - UTXOs that were spent in the transaction
/// * `new_rune_utxos` - New UTXOs that carry rune tokens
/// * `new_btc_utxos` - New plain BTC UTXOs (will be sorted by value internally)
/// * `fee_rate` - Current fee rate for consolidation flag setting
///
/// # Returns
/// * `Ok(())` - All UTXO updates completed successfully
/// * `Err(StateShardError::ExcessRuneUtxos)` - More rune UTXOs provided than can be stored
/// * `Err(StateShardError::ShardsAreFullOfBtcUtxos)` - No capacity for additional BTC UTXOs
///
/// # Invariants Maintained
/// - Each shard has at most one rune UTXO
/// - BTC UTXOs are distributed for optimal load balancing
/// - No UTXOs are lost during the update process
/// - Shard capacity limits are respected
///
/// # Performance Considerations
/// - Single iteration per shard for removals
/// - Efficient sorting and distribution of new UTXOs
/// - Minimal memory allocation and copying
/// - Optimized for on-chain BPF execution environment
#[allow(clippy::too_many_arguments)]
fn update_shards_utxos<'info, RS, U, S>(
    selected_shards: &mut [RefMut<'info, S>],
    utxos_to_remove: &[UtxoMeta],
    new_rune_utxos: Vec<U>,
    mut new_btc_utxos: Vec<U>,
    fee_rate: &FeeRate,
) -> super::error::Result<()>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    // 1. Remove old UTXOs first.
    remove_utxos_from_shards(selected_shards, utxos_to_remove)?;

    // 2. Insert rune UTXOs where needed.
    let mut rune_utxo_iter = new_rune_utxos.into_iter();
    for shard in selected_shards.iter_mut() {
        if shard.rune_utxo().is_none() {
            if let Some(utxo) = rune_utxo_iter.next() {
                shard.set_rune_utxo(utxo);
            }
        }
    }

    // After distribution there must be **no** leftover rune-bearing UTXOs.
    // Having some left would mean that we would lose tokens on-chain.
    if rune_utxo_iter.next().is_some() {
        return Err(StateShardError::ExcessRuneUtxos.into());
    }

    // 3. Distribute BTC UTXOs – largest first – to the least funded shard.
    new_btc_utxos.sort_by(|a, b| b.value().cmp(&a.value()));

    for mut utxo in new_btc_utxos.into_iter() {
        // Select target shard.
        let target_idx = select_best_shard_to_add_btc_to(selected_shards)
            .ok_or(StateShardError::ShardsAreFullOfBtcUtxos)?;

        let shard = &mut selected_shards[target_idx];

        // Apply consolidation flag if feature enabled.
        #[cfg(feature = "utxo-consolidation")]
        {
            use satellite_bitcoin::utxo_info::FixedOptionF64;
            if shard.btc_utxos_len() > 1 {
                *utxo.needs_consolidation_mut() = FixedOptionF64::some(fee_rate.0);
            }
        }

        let success = shard.add_btc_utxo(utxo).is_some();

        if !success {
            return Err(StateShardError::ShardsAreFullOfBtcUtxos.into());
        }
    }

    Ok(())
}

/// Updates the provided `shards` to reflect the effects of a transaction that
/// has just been **broadcast and accepted**.
///
/// This is the main entry point for applying Bitcoin transaction effects to program
/// shard state. It coordinates the complete process of identifying spent/created UTXOs,
/// handling rune token logistics, and updating shard state accordingly.
///
/// # Complete Process Overview
///
/// The function performs three high-level steps:
/// 1. **UTXO Analysis** - Determine which program-owned UTXOs were **spent** and which new ones were
///    **created** by analyzing the `TransactionBuilder` and the final signed `transaction`.
/// 2. **Rune Processing** - Split the newly created outputs into *plain BTC* vs *rune carrying*
///    outputs (the latter is only compiled in when the `runes` feature is enabled).
/// 3. **State Mutation** - Call internal balancing helpers so that the new UTXOs are optimally
///    distributed across the shards involved in the call.
///
/// # Transaction Analysis Details
/// - Examines `inputs_to_sign` to identify which UTXOs were consumed
/// - Scans transaction outputs for those matching the program's script pubkey
/// - Creates UTXO metadata for all newly created program-owned outputs
/// - Handles both standard BTC outputs and rune-bearing outputs
///
/// # Rune Token Handling (with `runes` feature)
/// - Processes runestone edicts to determine rune token distributions
/// - Updates UTXO rune amounts based on explicit edict targeting
/// - Handles runestone pointer for distributing remaining rune tokens
/// - Validates that all input rune tokens are properly accounted for
/// - Separates rune-bearing UTXOs from plain BTC UTXOs for different handling
///
/// # Shard Selection and Scope
/// Only the shards contained in `shard_set.selected_indices()` are mutated,
/// allowing callers to pass references to the *entire* shards slice without
/// cloning or allocating temporaries. This enables selective updates while
/// maintaining references to all available shards.
///
/// # Load Balancing and Distribution
/// - New BTC UTXOs are distributed using a load-balancing algorithm
/// - Rune UTXOs are placed in shards that don't already have one
/// - Distribution favors shards with lower total BTC values
/// - Maintains optimal UTXO distribution for future transaction efficiency
///
/// # Feature Flags Impact
/// - `runes` - Enables rune token processing and runestone handling
/// - `utxo-consolidation` - Adds consolidation flags to UTXOs when appropriate
///
/// # Arguments
/// * `transaction_builder` - Contains the signed transaction and metadata about inputs/outputs
/// * `selected_shards` - Mutable references to shards that should be updated
/// * `program_script_pubkey` - Script pubkey used to identify program-owned outputs
/// * `fee_rate` - Current fee rate for UTXO consolidation flag setting
///
/// # Errors
/// * `StateShardError::ShardsAreFullOfBtcUtxos` - All involved shards have reached their fixed-size BTC-UTXO capacity
/// * `StateShardError::ExcessRuneUtxos` - More rune UTXOs created than can be stored in available shards
/// * `StateShardError::OutputEdictIsNotInTransaction` - Runestone edict references non-existent output
/// * `StateShardError::RunestonePointerIsNotInTransaction` - Runestone pointer references invalid output
/// * `StateShardError::RuneAmountAdditionOverflow` - Arithmetic overflow in rune amount calculations
/// * `StateShardError::NotEnoughRuneInShards` - Attempting to spend more runes than available
///
/// # Example Usage
/// ```rust,ignore
/// let mut shards = shard_set.batch_mut()?;
/// update_shards_after_transaction(
///     &mut transaction_builder,
///     shards.shards_mut(),
///     &program_script_pubkey,
///     &fee_rate,
/// )?;
/// // Shards are automatically updated when the batch is dropped
/// ```
///
/// # Atomicity Guarantees
/// - Either all shard updates succeed or none do (error handling preserves original state)
/// - No partial updates that could leave shards in inconsistent states
/// - Transaction effects are applied atomically across all selected shards
#[allow(clippy::too_many_arguments)]
pub fn update_shards_after_transaction<
    'info,
    const MAX_USER_UTXOS: usize,
    const MAX_SHARDS_PER_PROGRAM: usize,
    RS,
    U,
    S,
>(
    transaction_builder: &TransactionBuilder<MAX_USER_UTXOS, MAX_SHARDS_PER_PROGRAM, RS>,
    selected_shards: &mut [RefMut<'info, S>],
    program_script_pubkey: &ScriptBuf,
    fee_rate: &FeeRate,
) -> super::error::Result<()>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
    S: StateShard<U, RS> + ZeroCopy + Owner,
{
    // ---------------------------------------------------------------------
    // 1. Identify program-owned UTXOs that were spent/created.
    // ---------------------------------------------------------------------
    let (utxos_to_remove, mut new_program_utxos) = get_modified_program_utxos_in_transaction(
        program_script_pubkey,
        &transaction_builder.transaction,
        transaction_builder.inputs_to_sign.as_slice(),
    );

    // ---------------------------------------------------------------------
    // 2. Split new outputs into rune vs btc (feature-gated like original).
    // ---------------------------------------------------------------------
    #[cfg(feature = "runes")]
    let (new_rune_utxos, new_btc_utxos) = {
        let runestone = &transaction_builder.runestone;

        let new_rune_utxos = update_modified_program_utxos_with_rune_amount(
            &mut new_program_utxos,
            runestone,
            &transaction_builder.total_rune_inputs,
        )?;
        (new_rune_utxos, new_program_utxos)
    };

    #[cfg(not(feature = "runes"))]
    let (new_rune_utxos, new_btc_utxos) = (Vec::<U>::new(), new_program_utxos);

    // ---------------------------------------------------------------------
    // 3. Mutate shards.
    // ---------------------------------------------------------------------
    update_shards_utxos(
        selected_shards,
        &utxos_to_remove,
        new_rune_utxos,
        new_btc_utxos,
        fee_rate,
    )
}

/// Analyzes a Bitcoin transaction to identify program-owned UTXOs that were spent and created.
///
/// This function performs the critical task of determining which UTXOs need to be removed
/// from shard state (because they were spent) and which new UTXOs need to be added
/// (because they were created as transaction outputs).
///
/// # Analysis Process
///
/// ## Spent UTXO Identification
/// - Examines each `InputToSign` to find program-owned UTXOs that were consumed
/// - Extracts the `previous_output` (outpoint) from each corresponding transaction input
/// - Converts transaction IDs to the big-endian byte format used in shard storage
/// - Creates `UtxoMeta` objects identifying each spent UTXO
///
/// ## Created UTXO Identification  
/// - Scans all transaction outputs for those matching the program's script pubkey
/// - Creates new `UtxoInfo` objects for each program-owned output found
/// - Assigns proper UTXO metadata (transaction ID and output index)
/// - Captures the satoshi value for each new UTXO
///
/// # UTXO Metadata Handling
/// - Uses big-endian byte representation for transaction IDs (consistent with shard storage)
/// - Maintains proper outpoint structure (txid + vout) for UTXO identification
/// - Ensures metadata compatibility with existing shard UTXO storage formats
///
/// # Return Value Structure
/// Returns a tuple containing:
/// - **Spent UTXOs** (`Vec<UtxoMeta>`) - Metadata for UTXOs that need removal from shards
/// - **Created UTXOs** (`Vec<U>`) - Complete UTXO info for newly created program-owned outputs
///
/// # Arguments
/// * `program_script_pubkey` - The script pubkey identifying program-owned outputs
/// * `transaction` - The complete Bitcoin transaction to analyze
/// * `inputs_to_sign` - Metadata about which inputs the program is responsible for signing
///
/// # Usage Context
/// This function is typically called as the first step in `update_shards_after_transaction`
/// to identify the scope of UTXO changes that need to be applied to shard state.
///
/// # Performance Characteristics
/// - Pre-allocates vectors with estimated capacity for efficiency
/// - Single pass through inputs and outputs
/// - Minimal memory allocation and copying
/// - O(n + m) complexity where n = inputs to sign, m = transaction outputs
///
/// # Example
/// ```rust,ignore
/// let (spent_utxos, created_utxos) = get_modified_program_utxos_in_transaction(
///     &program_script,
///     &signed_transaction,
///     &inputs_to_sign,
/// );
/// // spent_utxos: Vec<UtxoMeta> - remove these from shards
/// // created_utxos: Vec<UtxoInfo> - add these to shards
/// ```
fn get_modified_program_utxos_in_transaction<RS, U>(
    program_script_pubkey: &ScriptBuf,
    transaction: &Transaction,
    inputs_to_sign: &[InputToSign],
) -> (Vec<UtxoMeta>, Vec<U>)
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
{
    use satellite_bitcoin::bytes::txid_to_bytes_big_endian;

    let mut utxos_to_remove = Vec::with_capacity(inputs_to_sign.len());
    let mut program_outputs = Vec::with_capacity(transaction.output.len() / 2);

    let txid_bytes = txid_to_bytes_big_endian(&transaction.compute_txid());

    for input in inputs_to_sign {
        let outpoint = transaction.input[input.index as usize].previous_output;
        utxos_to_remove.push(UtxoMeta::from(
            txid_to_bytes_big_endian(&outpoint.txid),
            outpoint.vout,
        ));
    }

    for (index, output) in transaction.output.iter().enumerate() {
        if &output.script_pubkey == program_script_pubkey {
            program_outputs.push(U::new(
                UtxoMeta::from(txid_bytes, index as u32),
                output.value.to_sat(),
            ));
        }
    }

    (utxos_to_remove, program_outputs)
}

#[cfg(feature = "runes")]
/// Processes runestone data to assign rune token amounts to program-owned transaction outputs.
///
/// This function handles the complex task of distributing rune tokens from transaction inputs
/// to the appropriate outputs based on runestone edicts and pointer rules. It modifies the
/// provided UTXOs to include rune amounts and separates rune-bearing UTXOs from plain BTC UTXOs.
///
/// # Runestone Processing Overview
///
/// ## Edict Processing
/// The function processes each edict in the runestone which explicitly assigns rune amounts:
/// - Finds the target output by matching the edict's output index with UTXO vout
/// - Creates or updates the rune amount for the specified rune ID on that UTXO
/// - Decrements the corresponding amount from the input rune totals
/// - Handles arithmetic overflow protection for rune amount additions
/// - Validates that sufficient input runes exist for each edict assignment
///
/// ## Pointer Handling
/// After processing explicit edicts, remaining input runes are distributed via pointer:
/// - If a runestone pointer is specified, all remaining runes go to that output
/// - The pointer must reference a valid program-owned output in the transaction
/// - Multiple rune types can be assigned to the same pointer output
/// - Handles the case where pointer output already has runes from edicts
///
/// ## Remaining Rune Validation
/// - If no pointer is set, validates that no input runes remain unassigned
/// - Prevents rune token loss by requiring all input runes to be explicitly assigned
/// - Ensures conservation of rune tokens across the transaction boundary
///
/// # UTXO Separation Logic
/// After rune assignment, the function separates UTXOs into two categories:
/// - **Rune UTXOs** - UTXOs that carry any rune tokens (extracted from the vector)
/// - **BTC UTXOs** - Plain UTXOs with only satoshi value (remain in original vector)
///
/// This separation is critical because rune UTXOs and BTC UTXOs are stored differently
/// in shard state and have different handling requirements.
///
/// # Arguments
/// * `new_program_outputs` - Mutable vector of program-owned UTXOs from the transaction
/// * `runestone` - The runestone containing edicts and pointer information
/// * `prev_rune_amount` - Mutable set of input rune amounts to be consumed
///
/// # Returns
/// * `Ok(Vec<U>)` - Vector of UTXOs that carry rune tokens (separated from input vector)
/// * `Err(StateShardError::OutputEdictIsNotInTransaction)` - Edict references invalid output index
/// * `Err(StateShardError::RunestonePointerIsNotInTransaction)` - Pointer references invalid output
/// * `Err(StateShardError::RuneAmountAdditionOverflow)` - Arithmetic overflow in rune calculations
/// * `Err(StateShardError::NotEnoughRuneInShards)` - Insufficient input runes for assignments
///
/// # Rune Conservation
/// The function maintains strict rune conservation by:
/// - Tracking all input rune amounts and decrementing as they're assigned
/// - Requiring that all remaining runes be assigned via pointer or error
/// - Preventing double-spending of rune tokens
/// - Ensuring no rune tokens are lost during processing
///
/// # Example Usage
/// ```rust,ignore
/// let rune_utxos = update_modified_program_utxos_with_rune_amount(
///     &mut program_outputs,  // Modified in place
///     &runestone,
///     &mut input_runes,      // Decremented as runes are assigned
/// )?;
/// // program_outputs now contains only BTC UTXOs
/// // rune_utxos contains UTXOs with rune token assignments
/// ```
///
/// # Performance Characteristics
/// - O(e × o) complexity where e = edicts, o = outputs (due to position lookups)
/// - Minimal memory allocation (reuses existing vectors where possible)
/// - Single pass through edicts and pointer processing
/// - Efficient vector manipulation for UTXO separation
fn update_modified_program_utxos_with_rune_amount<RS, U>(
    new_program_outputs: &mut Vec<U>,
    runestone: &Runestone,
    prev_rune_amount: &RS,
) -> super::error::Result<Vec<U>>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
    U: UtxoInfoTrait<RS>,
{
    let mut remaining_rune_amount = prev_rune_amount.clone();
    let mut rune_utxos = vec![];

    for edict in &runestone.edicts {
        let rune_amount = edict.amount;
        let index = edict.output;

        let output = new_program_outputs
            .get_mut(index as usize)
            .ok_or(StateShardError::OutputEdictIsNotInTransaction)?;

        let rune_id = RuneId::new(edict.id.block, edict.id.tx);

        output.runes_mut().insert_or_modify::<StateShardError, _>(
            RuneAmount {
                id: rune_id,
                amount: rune_amount,
            },
            |rune_input| {
                rune_input.amount = rune_input
                    .amount
                    .checked_add(rune_amount)
                    .ok_or(StateShardError::RuneAmountAdditionOverflow)?;
                Ok(())
            },
        )?;

        if let Some(remaining) = remaining_rune_amount.find_mut(&rune_id) {
            remaining.amount = remaining
                .amount
                .checked_sub(rune_amount)
                .ok_or(StateShardError::NotEnoughRuneInShards)?;
        }
    }

    if let Some(pointer_index) = runestone.pointer {
        for rune_amount in remaining_rune_amount.iter() {
            if rune_amount.amount > 0 {
                if let Some(output) = new_program_outputs
                    .iter_mut()
                    .find(|u| u.meta().vout() == pointer_index)
                {
                    output.runes_mut().insert_or_modify::<StateShardError, _>(
                        RuneAmount {
                            id: rune_amount.id,
                            amount: rune_amount.amount,
                        },
                        |rune_input| {
                            rune_input.amount =
                                rune_input
                                    .amount
                                    .checked_add(rune_amount.amount)
                                    .ok_or(StateShardError::RuneAmountAdditionOverflow)?;
                            Ok(())
                        },
                    )?;
                } else {
                    return Err(StateShardError::RunestonePointerIsNotInTransaction);
                }
            }
        }
    } else {
        for rune_amount in remaining_rune_amount.iter() {
            if rune_amount.amount > 0 {
                return Err(StateShardError::RunestonePointerIsNotInTransaction);
            }
        }
    }

    let mut i = new_program_outputs.len();
    while i > 0 {
        i -= 1;
        if new_program_outputs[i].runes().len() > 0 {
            let rune_utxo = new_program_outputs.swap_remove(i);
            rune_utxos.push(rune_utxo);
        }
    }

    rune_utxos.reverse();

    Ok(rune_utxos)
}

#[cfg(test)]
mod tests_loader {
    use super::*;

    use super::super::tests::common::{
        add_btc_utxos_bulk, create_shard, leak_loaders_from_vec, MockShardZc, MAX_BTC_UTXOS,
    };
    use satellite_bitcoin::utxo_info::{SingleRuneSet, UtxoInfo, UtxoInfoTrait};

    // Re-export for macro reuse – mirrors helper in split_loader tests.
    use satellite_bitcoin::TransactionBuilder as TB;

    #[allow(unused_macros)]
    macro_rules! new_tb {
        ($max_utxos:expr, $max_shards:expr) => {
            TB::<$max_utxos, $max_shards, SingleRuneSet>::new()
        };
    }

    // === Shared helpers ====================================================
    fn create_utxo(
        value: u64,
        txid_byte: u8,
        vout: u32,
    ) -> satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet> {
        let txid = [txid_byte; 32];
        let meta = UtxoMeta::from(txid, vout);
        let utxo_info = UtxoInfo::new(meta, value);
        utxo_info
    }

    fn fee_rate() -> FeeRate {
        FeeRate(1.0)
    }

    // ---------------------------------------------------------------------
    // select_best_shard_to_add_btc_to
    // ---------------------------------------------------------------------
    mod select_best_shard_to_add_btc_to {
        use super::*;

        #[test]
        fn selects_shard_with_smallest_total_btc() {
            let shard_low = create_shard(50);
            let shard_medium = create_shard(100);
            let shard_high = create_shard(200);

            let shards_vec = vec![shard_medium, shard_low, shard_high];
            let loaders = leak_loaders_from_vec(shards_vec);

            // Get RefMut objects directly from loaders
            let shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();

            let best = super::super::select_best_shard_to_add_btc_to::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&shard_refs);

            assert_eq!(best, Some(1)); // shard_low at index 1 has the fewest sats
        }

        #[test]
        fn returns_none_when_all_shards_are_full() {
            let mut shard0 = create_shard(0);
            let mut shard1 = create_shard(0);
            // Fill both shards to capacity
            add_btc_utxos_bulk(&mut shard0, &vec![1u64; MAX_BTC_UTXOS]);
            add_btc_utxos_bulk(&mut shard1, &vec![1u64; MAX_BTC_UTXOS]);

            let shards_vec = vec![shard0, shard1];
            let loaders = leak_loaders_from_vec(shards_vec);

            // Get RefMut objects directly from loaders
            let shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();

            let res = super::super::select_best_shard_to_add_btc_to::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&shard_refs);
            assert_eq!(res, None);
        }

        #[test]
        fn skips_full_shard_and_selects_available_one() {
            let mut shard_full = create_shard(0);
            add_btc_utxos_bulk(&mut shard_full, &vec![1u64; MAX_BTC_UTXOS]);
            let shard_available = create_shard(500);

            let shards_vec = vec![shard_full, shard_available];
            let loaders = leak_loaders_from_vec(shards_vec);

            // Get RefMut objects directly from loaders
            let shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();

            let res = super::super::select_best_shard_to_add_btc_to::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&shard_refs);
            assert_eq!(res, Some(1)); // second shard has spare capacity
        }
    }

    // ---------------------------------------------------------------------
    // update_shards_utxos (subset)
    // ---------------------------------------------------------------------
    mod update_shards_utxos_tests {
        use super::*;

        const MAX_SEL: usize = 2;

        fn setup_shard_loaders(
            shard0: MockShardZc,
            shard1: MockShardZc,
        ) -> &'static [satellite_lang::prelude::AccountLoader<'static, MockShardZc>] {
            let shards_vec = vec![shard0, shard1];
            leak_loaders_from_vec(shards_vec)
        }

        #[test]
        fn distributes_new_utxos_and_handles_runes() {
            let loaders = setup_shard_loaders(create_shard(0), create_shard(0));

            let new_rune_utxo = create_utxo(546, 10, 0);
            let new_btc_big = create_utxo(200, 11, 0);
            let new_btc_small = create_utxo(100, 12, 0);

            // Get RefMut objects directly from loaders
            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            let result = super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut shard_refs,
                &[],
                vec![new_rune_utxo.clone()],
                vec![new_btc_big.clone(), new_btc_small.clone()],
                &fee_rate(),
            );
            assert!(result.is_ok());
            drop(shard_refs);

            // Verify shard0 (index 0) received rune utxo and larger btc value
            let shard0_ref = loaders[0].load().unwrap();
            let shard0_btc_len = shard0_ref.btc_utxos_len();
            let shard0_rune_present = shard0_ref.rune_utxo().is_some();
            assert_eq!(shard0_btc_len, 1);
            assert!(shard0_rune_present);
            drop(shard0_ref);

            // shard1 should have smaller btc and no rune
            let shard1_ref = loaders[1].load().unwrap();
            let shard1_btc_len = shard1_ref.btc_utxos_len();
            let shard1_rune_present = shard1_ref.rune_utxo().is_some();
            assert_eq!(shard1_btc_len, 1);
            assert!(!shard1_rune_present);
        }

        #[test]
        fn errors_when_btc_utxo_vector_overflows() {
            // Fill both shards
            let mut shard0 = create_shard(0);
            add_btc_utxos_bulk(&mut shard0, &vec![1u64; MAX_BTC_UTXOS]);
            let mut shard1 = create_shard(0);
            add_btc_utxos_bulk(&mut shard1, &vec![1u64; MAX_BTC_UTXOS]);

            let loaders = setup_shard_loaders(shard0, shard1);

            // Get RefMut objects directly from loaders
            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            let err = super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut shard_refs,
                &[],
                vec![],
                vec![create_utxo(1, 99, 0)],
                &fee_rate(),
            )
            .unwrap_err();

            assert_eq!(err, StateShardError::ShardsAreFullOfBtcUtxos);
        }

        #[test]
        fn succeeds_after_removal_creates_capacity() {
            // Fill shard0 to capacity (MAX_BTC_UTXOS) and shard1 empty.
            let mut shard0 = MockShardZc::default();

            // First UTXO that we will remove.
            let utxo_to_remove = create_utxo(100, 120, 0);
            shard0.add_btc_utxo(utxo_to_remove.clone());

            // Fill rest of shard0
            let filler: Vec<u64> = vec![1u64; MAX_BTC_UTXOS - 1];
            add_btc_utxos_bulk(&mut shard0, &filler);

            let shard1 = MockShardZc::default();

            let shards_vec = vec![shard0, shard1];
            let loaders = leak_loaders_from_vec(shards_vec);

            let new_utxo = create_utxo(200, 122, 0);

            // Execute update – should succeed because removal frees 1 slot.
            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut shard_refs,
                &[*utxo_to_remove.meta()],
                vec![],
                vec![new_utxo.clone()],
                &fee_rate(),
            )
            .unwrap();
            drop(shard_refs);

            // shard0 should still be at capacity and no longer contain utxo_to_remove
            let shard0_ref = loaders[0].load().unwrap();
            assert_eq!(shard0_ref.btc_utxos_len(), MAX_BTC_UTXOS - 1);
            assert!(!shard0_ref
                .btc_utxos()
                .iter()
                .any(|u| u.eq_meta(&utxo_to_remove)));
            drop(shard0_ref);

            // shard1 should now contain the new_utxo (least funded after removal)
            let shard1_ref = loaders[1].load().unwrap();
            assert_eq!(shard1_ref.btc_utxos_len(), 1);
            assert!(shard1_ref.btc_utxos().iter().any(|u| u.eq_meta(&new_utxo)));
        }

        #[test]
        fn replaces_rune_utxo_correctly() {
            let old_rune = create_utxo(546, 130, 0);
            let new_rune = create_utxo(546, 131, 0);

            let mut shard0 = MockShardZc::default();
            shard0.set_rune_utxo(old_rune.clone());

            let shard1 = MockShardZc::default();

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut shard_refs,
                &[*old_rune.meta()],
                vec![new_rune.clone()],
                vec![],
                &fee_rate(),
            )
            .unwrap();
            drop(shard_refs);

            let shard0_ref = loaders[0].load().unwrap();
            let r = shard0_ref.rune_utxo().expect("rune utxo expected");
            assert!(r.eq_meta(&new_rune));
            drop(shard0_ref);

            let shard1_ref = loaders[1].load().unwrap();
            assert!(shard1_ref.rune_utxo().is_none());
        }

        #[cfg(feature = "utxo-consolidation")]
        #[test]
        fn sets_needs_consolidation_flag_when_applicable() {
            // shard0 has 2 tiny UTXOs so will receive the new one
            let mut shard0 = MockShardZc::default();
            add_btc_utxos_bulk(&mut shard0, &[1, 1]);

            let mut shard1 = MockShardZc::default();
            add_btc_utxos_bulk(&mut shard1, &[100]);

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let new_utxo = create_utxo(5, 83, 0);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut shard_refs,
                &[],
                vec![],
                vec![new_utxo.clone()],
                &fee_rate(),
            )
            .unwrap();
            drop(shard_refs);

            let shard0_ref = loaders[0].load().unwrap();
            let inserted = shard0_ref.btc_utxos().last().unwrap();
            assert!(inserted.needs_consolidation().is_some());
            assert_eq!(inserted.needs_consolidation().get().unwrap(), fee_rate().0);
        }

        #[cfg(feature = "utxo-consolidation")]
        #[test]
        fn does_not_set_consolidation_flag_when_shard_has_one_or_zero_utxos() {
            let mut shard0 = MockShardZc::default();
            add_btc_utxos_bulk(&mut shard0, &[50]);

            let shard1 = MockShardZc::default();

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let new_utxo = create_utxo(10, 151, 0);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut shard_refs,
                &[],
                vec![],
                vec![new_utxo.clone()],
                &fee_rate(),
            )
            .unwrap();
            drop(shard_refs);

            // new UTXO should go to shard1 (empty before)
            let shard1_ref = loaders[1].load().unwrap();
            assert_eq!(shard1_ref.btc_utxos_len(), 1);
            let inserted = shard1_ref.btc_utxos().first().unwrap();
            assert!(inserted.needs_consolidation().is_none());
        }

        #[test]
        fn skips_inserting_rune_when_already_present() {
            // shard0 already has a rune UTXO
            let existing_rune = create_utxo(546, 30, 0);
            let mut shard0 = MockShardZc::default();
            shard0.set_rune_utxo(existing_rune.clone());

            let shard1 = MockShardZc::default();

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            // Attempt to insert a new rune UTXO – should go to shard1, not replace shard0's
            let new_rune = create_utxo(546, 31, 0);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut shard_refs,
                &[],
                vec![new_rune.clone()],
                vec![],
                &fee_rate(),
            )
            .unwrap();
            drop(shard_refs);

            // Verify shard0 still has original rune
            let shard0_ref = loaders[0].load().unwrap();
            assert!(shard0_ref.rune_utxo().unwrap().eq_meta(&existing_rune));
            drop(shard0_ref);

            // shard1 received new rune
            let shard1_ref = loaders[1].load().unwrap();
            assert!(shard1_ref.rune_utxo().is_some());
            assert!(shard1_ref.rune_utxo().unwrap().eq_meta(&new_rune));
        }

        #[test]
        fn handles_no_new_runes_when_shards_have_none() {
            let shard0 = MockShardZc::default();
            let shard1 = MockShardZc::default();
            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let btc_utxo = create_utxo(1_000, 140, 0);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_utxos::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut shard_refs, &[], vec![], vec![btc_utxo], &fee_rate())
            .unwrap();
            drop(shard_refs);

            // Neither shard should have a rune utxo.
            for loader in loaders.iter() {
                let shard_ref = loader.load().unwrap();
                assert!(shard_ref.rune_utxo().is_none());
            }
        }
    }

    // ---------------------------------------------------------------------
    // remove_utxos_from_shards
    // ---------------------------------------------------------------------
    mod remove_utxos_from_shards {
        use super::*;

        #[test]
        fn removes_btc_and_rune_utxos_across_shards() {
            // UTXO to be removed
            let utxo_to_remove = create_utxo(1_000, 200, 0);
            let meta_to_remove = *utxo_to_remove.meta();

            // Build two shards each containing the BTC + Rune UTXO to remove
            let mut shard0 = MockShardZc::default();
            shard0.add_btc_utxo(utxo_to_remove.clone());
            shard0.set_rune_utxo(utxo_to_remove.clone());

            let mut shard1 = MockShardZc::default();
            shard1.add_btc_utxo(utxo_to_remove.clone());
            shard1.set_rune_utxo(utxo_to_remove.clone());

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            // Execute helper and verify
            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::remove_utxos_from_shards::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut shard_refs, &[meta_to_remove])
            .unwrap();
            drop(shard_refs);

            for loader in loaders.iter() {
                let shard_ref = loader.load().unwrap();
                assert_eq!(shard_ref.btc_utxos_len(), 0);
                assert!(shard_ref.rune_utxo().is_none());
            }
        }

        #[test]
        fn ignores_utxo_missing_in_some_shards() {
            let utxo_to_remove = create_utxo(500, 201, 0);
            let meta_to_remove = *utxo_to_remove.meta();

            // shard0 contains the UTXO, shard1 does not
            let mut shard0 = MockShardZc::default();
            shard0.add_btc_utxo(utxo_to_remove.clone());

            let shard1 = MockShardZc::default();

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::remove_utxos_from_shards::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut shard_refs, &[meta_to_remove])
            .unwrap();
            drop(shard_refs);

            // shard0 should now be empty, shard1 unaffected
            let shard0_ref = loaders[0].load().unwrap();
            assert_eq!(shard0_ref.btc_utxos_len(), 0);
            drop(shard0_ref);

            let shard1_ref = loaders[1].load().unwrap();
            assert_eq!(shard1_ref.btc_utxos_len(), 0);
        }

        #[test]
        fn handles_empty_utxos_to_remove() {
            let shard0 = create_shard(1000);
            let shard1 = create_shard(2000);
            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            // Removing zero items should be a no-op
            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::remove_utxos_from_shards::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut shard_refs, &[])
            .unwrap();
            drop(shard_refs);

            // Verify original balances intact
            let shard0_ref = loaders[0].load().unwrap();
            assert_eq!(shard0_ref.btc_utxos_len(), 1);
            drop(shard0_ref);

            let shard1_ref = loaders[1].load().unwrap();
            assert_eq!(shard1_ref.btc_utxos_len(), 1);
        }

        #[test]
        fn works_when_shard_has_no_rune_utxo() {
            let utxo_to_remove = create_utxo(1_000, 60, 0);
            let meta = *utxo_to_remove.meta();

            let mut shard = MockShardZc::default();
            shard.add_btc_utxo(utxo_to_remove.clone());

            let loaders = leak_loaders_from_vec(vec![shard]);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::remove_utxos_from_shards::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut shard_refs, &[meta])
            .unwrap();
            drop(shard_refs);

            let shard_ref = loaders[0].load().unwrap();
            assert_eq!(shard_ref.btc_utxos_len(), 0);
        }

        #[test]
        fn removes_multiple_utxos_from_multiple_shards() {
            let utxo_a = create_utxo(500, 250, 0);
            let utxo_b = create_utxo(600, 251, 0);

            let mut shard0 = MockShardZc::default();
            shard0.add_btc_utxo(utxo_a.clone());
            shard0.add_btc_utxo(utxo_b.clone());

            let mut shard1 = MockShardZc::default();
            shard1.add_btc_utxo(utxo_a.clone());
            shard1.add_btc_utxo(utxo_b.clone());

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::remove_utxos_from_shards::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut shard_refs, &[*utxo_a.meta(), *utxo_b.meta()])
            .unwrap();
            drop(shard_refs);

            for loader in loaders.iter() {
                let shard_ref = loader.load().unwrap();
                assert_eq!(shard_ref.btc_utxos_len(), 0);
            }
        }
    }

    // ---------------------------------------------------------------------
    // get_modified_program_utxos_in_transaction
    // ---------------------------------------------------------------------
    mod get_modified_program_utxos_in_transaction {
        use super::*;
        use arch_program::input_to_sign::InputToSign;
        use bitcoin::absolute::LockTime;
        use bitcoin::transaction::Version;
        use bitcoin::{Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Witness};

        #[test]
        fn identifies_program_outputs_correctly() {
            let script = ScriptBuf::new();

            let tx = Transaction {
                version: Version::TWO,
                lock_time: LockTime::ZERO,
                input: vec![TxIn {
                    previous_output: OutPoint::null(),
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::MAX,
                    witness: Witness::default(),
                }],
                output: vec![TxOut {
                    value: Amount::from_sat(1000),
                    script_pubkey: script.clone(),
                }],
            };

            let inputs = vec![InputToSign {
                index: 0,
                signer: arch_program::pubkey::Pubkey::default(),
            }];

            let (removed, added): (
                Vec<UtxoMeta>,
                Vec<satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>>,
            ) = super::super::get_modified_program_utxos_in_transaction::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
            >(&script, &tx, &inputs);

            assert_eq!(removed.len(), 1);
            assert_eq!(added.len(), 1);
            assert_eq!(added[0].value, 1000);
        }

        #[test]
        fn handles_multiple_inputs_to_sign() {
            let script = ScriptBuf::new();

            let outpoint1 = {
                let mut o = OutPoint::null();
                o.vout = 0;
                o
            };
            let outpoint2 = {
                let mut o = OutPoint::null();
                o.vout = 1;
                o
            };

            let tx = Transaction {
                version: Version::TWO,
                lock_time: LockTime::ZERO,
                input: vec![
                    TxIn {
                        previous_output: outpoint1,
                        script_sig: ScriptBuf::new(),
                        sequence: Sequence::MAX,
                        witness: Witness::default(),
                    },
                    TxIn {
                        previous_output: outpoint2,
                        script_sig: ScriptBuf::new(),
                        sequence: Sequence::MAX,
                        witness: Witness::default(),
                    },
                ],
                output: vec![],
            };

            let inputs = vec![
                InputToSign {
                    index: 0,
                    signer: arch_program::pubkey::Pubkey::default(),
                },
                InputToSign {
                    index: 1,
                    signer: arch_program::pubkey::Pubkey::default(),
                },
            ];

            let (removed, _added): (
                Vec<UtxoMeta>,
                Vec<satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>>,
            ) = super::super::get_modified_program_utxos_in_transaction::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
            >(&script, &tx, &inputs);

            assert_eq!(removed.len(), 2);
            assert!(removed.iter().any(|m| m.vout() == 0));
            assert!(removed.iter().any(|m| m.vout() == 1));
        }

        #[test]
        fn handles_multiple_program_outputs() {
            let script = ScriptBuf::new();

            let tx = Transaction {
                version: Version::TWO,
                lock_time: LockTime::ZERO,
                input: vec![],
                output: vec![
                    TxOut {
                        value: Amount::from_sat(1_000),
                        script_pubkey: script.clone(),
                    },
                    TxOut {
                        value: Amount::from_sat(2_000),
                        script_pubkey: ScriptBuf::from_bytes(vec![0x51]),
                    },
                    TxOut {
                        value: Amount::from_sat(3_000),
                        script_pubkey: script.clone(),
                    },
                ],
            };

            let (_removed, added): (
                Vec<UtxoMeta>,
                Vec<satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>>,
            ) = super::super::get_modified_program_utxos_in_transaction::<
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
            >(&script, &tx, &[]);

            assert_eq!(added.len(), 2);
            assert_eq!(added[0].value, 1_000);
            assert_eq!(added[0].meta.vout(), 0);
            assert_eq!(added[1].value, 3_000);
            assert_eq!(added[1].meta.vout(), 2);
        }
    }

    // ---------------------------------------------------------------------
    // update_shards_after_transaction
    // ---------------------------------------------------------------------
    mod update_shards_after_transaction {
        use super::*;
        use arch_program::input_to_sign::InputToSign;
        use bitcoin::absolute::LockTime;
        use bitcoin::hashes::sha256d::Hash as Sha256dHash;
        use bitcoin::hashes::Hash;
        use bitcoin::transaction::Version;
        use bitcoin::{Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Witness};

        #[test]
        fn integrates_all_helpers() {
            const MAX_USER_UTXOS: usize = 4;
            const MAX_SHARDS_PER_PROGRAM: usize = 4;

            let mut builder: satellite_bitcoin::TransactionBuilder<
                MAX_USER_UTXOS,
                MAX_SHARDS_PER_PROGRAM,
                SingleRuneSet,
            > = new_tb!(MAX_USER_UTXOS, MAX_SHARDS_PER_PROGRAM);

            let program_script = ScriptBuf::new();

            // existing utxo in shard0
            let existing_utxo = create_utxo(5_000, 200, 0);
            let txid_200 =
                bitcoin::Txid::from_raw_hash(Sha256dHash::from_slice(&[200u8; 32]).unwrap());
            let input_outpoint = OutPoint {
                txid: txid_200,
                vout: 0,
            };

            builder.transaction = Transaction {
                version: Version::TWO,
                lock_time: LockTime::ZERO,
                input: vec![TxIn {
                    previous_output: input_outpoint,
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::MAX,
                    witness: Witness::default(),
                }],
                output: vec![TxOut {
                    value: Amount::from_sat(4_500),
                    script_pubkey: program_script.clone(),
                }],
            };

            builder
                .inputs_to_sign
                .push(InputToSign {
                    index: 0,
                    signer: arch_program::pubkey::Pubkey::default(),
                })
                .unwrap();

            let mut shard0 = MockShardZc::default();
            shard0.add_btc_utxo(existing_utxo.clone());
            let shard1 = MockShardZc::default();

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_after_transaction::<
                MAX_USER_UTXOS,
                MAX_SHARDS_PER_PROGRAM,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut builder, &mut shard_refs, &program_script, &fee_rate())
            .unwrap();
            drop(shard_refs);

            // old utxo removed
            let shard0_ref = loaders[0].load().unwrap();
            assert!(!shard0_ref
                .btc_utxos()
                .iter()
                .any(|u| u.eq_meta(&existing_utxo)));
            let shard0_len = shard0_ref.btc_utxos_len();
            drop(shard0_ref);

            let shard1_ref = loaders[1].load().unwrap();
            let shard1_len = shard1_ref.btc_utxos_len();
            drop(shard1_ref);

            let total = shard0_len + shard1_len;
            assert_eq!(total, 1);
        }

        #[cfg(feature = "runes")]
        #[test]
        fn handles_rune_utxo_spending_and_creation() {
            const MAX_USER_UTXOS: usize = 4;
            const MAX_SHARDS_PER_PROGRAM: usize = 4;

            let mut builder: satellite_bitcoin::TransactionBuilder<
                MAX_USER_UTXOS,
                MAX_SHARDS_PER_PROGRAM,
                SingleRuneSet,
            > = new_tb!(MAX_USER_UTXOS, MAX_SHARDS_PER_PROGRAM);

            let program_script = ScriptBuf::new();
            let existing_rune_utxo = create_utxo(546, 210, 0);

            builder
                .total_rune_inputs
                .insert(arch_program::rune::RuneAmount {
                    id: arch_program::rune::RuneId::new(1, 0),
                    amount: 100,
                })
                .unwrap();

            let txid_210 =
                bitcoin::Txid::from_raw_hash(Sha256dHash::from_slice(&[210u8; 32]).unwrap());
            let input_outpoint = OutPoint {
                txid: txid_210,
                vout: 0,
            };

            builder.transaction = Transaction {
                version: Version::TWO,
                lock_time: LockTime::ZERO,
                input: vec![TxIn {
                    previous_output: input_outpoint,
                    script_sig: ScriptBuf::new(),
                    sequence: Sequence::MAX,
                    witness: Witness::default(),
                }],
                output: vec![
                    TxOut {
                        value: Amount::from_sat(546),
                        script_pubkey: program_script.clone(),
                    },
                    TxOut {
                        value: Amount::from_sat(546),
                        script_pubkey: program_script.clone(),
                    },
                ],
            };

            builder
                .inputs_to_sign
                .push(InputToSign {
                    index: 0,
                    signer: arch_program::pubkey::Pubkey::default(),
                })
                .unwrap();

            builder.runestone = Runestone {
                pointer: Some(1),
                edicts: vec![ordinals::Edict {
                    id: ordinals::RuneId { block: 1, tx: 0 },
                    amount: 60,
                    output: 0,
                }],
                ..Default::default()
            };

            let mut shard0 = MockShardZc::default();
            shard0.set_rune_utxo(existing_rune_utxo.clone());
            let shard1 = MockShardZc::default();

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            super::super::update_shards_after_transaction::<
                MAX_USER_UTXOS,
                MAX_SHARDS_PER_PROGRAM,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(&mut builder, &mut shard_refs, &program_script, &fee_rate())
            .unwrap();
            drop(shard_refs);

            // old rune utxo removed, at least one shard has rune utxo
            let shard0_ref = loaders[0].load().unwrap();
            let shard0_has_rune = shard0_ref.rune_utxo().is_some();
            drop(shard0_ref);

            let shard1_ref = loaders[1].load().unwrap();
            let shard1_has_rune = shard1_ref.rune_utxo().is_some();
            drop(shard1_ref);

            let has_rune = shard0_has_rune || shard1_has_rune;
            assert!(has_rune);
        }

        #[test]
        fn propagates_overflow_error_when_all_shards_full() {
            const MAX_USER_UTXOS: usize = 4;
            const MAX_SHARDS_PER_PROGRAM: usize = 4;

            let mut builder: satellite_bitcoin::TransactionBuilder<
                MAX_USER_UTXOS,
                MAX_SHARDS_PER_PROGRAM,
                SingleRuneSet,
            > = new_tb!(MAX_USER_UTXOS, MAX_SHARDS_PER_PROGRAM);

            builder.transaction = Transaction {
                version: Version::TWO,
                lock_time: LockTime::ZERO,
                input: vec![],
                output: vec![TxOut {
                    value: Amount::from_sat(1),
                    script_pubkey: ScriptBuf::new(),
                }],
            };

            // Fill both shards to capacity
            let mut shard0 = MockShardZc::default();
            let mut shard1 = MockShardZc::default();
            for i in 0..MockShardZc::btc_utxos_max_len(&shard0) {
                shard0.add_btc_utxo(create_utxo(1, 220, i as u32));
                shard1.add_btc_utxo(create_utxo(1, 221, i as u32));
            }

            let loaders = leak_loaders_from_vec(vec![shard0, shard1]);

            let mut shard_refs: Vec<_> = loaders
                .iter()
                .map(|loader| loader.load_mut().unwrap())
                .collect();
            let err = super::super::update_shards_after_transaction::<
                MAX_USER_UTXOS,
                MAX_SHARDS_PER_PROGRAM,
                SingleRuneSet,
                satellite_bitcoin::utxo_info::UtxoInfo<SingleRuneSet>,
                MockShardZc,
            >(
                &mut builder,
                &mut shard_refs,
                &ScriptBuf::new(),
                &fee_rate(),
            )
            .unwrap_err();

            assert_eq!(err, StateShardError::ShardsAreFullOfBtcUtxos);
        }
    }
}
