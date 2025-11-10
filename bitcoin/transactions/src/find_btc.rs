use arch_program::pubkey::Pubkey;
use satellite_collections::generic::fixed_list::FixedList;

use crate::btc_utxo_holder::BtcUtxoHolder;
use crate::constants::DUST_LIMIT;
use crate::error::BitcoinTxError;
use crate::mempool::TxStatus;
use crate::utxo_info::UtxoInfo;

use super::TransactionBuilder;

impl<'info, const MAX_MODIFIED_ACCOUNTS: usize, const MAX_INPUTS_TO_SIGN: usize, RuneSet>
    TransactionBuilder<'info, MAX_MODIFIED_ACCOUNTS, MAX_INPUTS_TO_SIGN, RuneSet>
where
    RuneSet: satellite_collections::generic::fixed_set::FixedCapacitySet<
            Item = arch_program::rune::RuneAmount,
        > + Default,
{
    /// Greedily selects UTXOs until at least `amount` satoshis are gathered.
    ///
    /// Returns the indices of the chosen items plus the total value selected.
    pub fn find_btc_in_utxos<T>(
        &mut self,
        utxos: &[T],
        program_info_pubkey: &Pubkey,
        amount: u64,
    ) -> Result<(Vec<usize>, u64), BitcoinTxError>
    where
        T: AsRef<UtxoInfo<RuneSet>>, // same RuneSet generic as builder
    {
        if amount == 0 {
            return Ok((Vec::new(), 0));
        }

        let mut btc_amount = 0;

        let mut consolidation_inputs_count: u32 = 0;
        let mut total_consolidation_input_amount: u64 = 0;

        // Create indices instead of cloning the entire vector
        let mut utxo_indices: Vec<usize> = (0..utxos.len()).collect();

        // Sort indices by prioritizing non-consolidation UTXOs and then by value (biggest first)
        #[cfg(feature = "utxo-consolidation")]
        utxo_indices.sort_by(|&a, &b| {
            use std::cmp::Ordering;

            let utxo_a = &utxos[a];
            let utxo_b = &utxos[b];

            match (
                utxo_a.as_ref().needs_consolidation.is_some(),
                utxo_b.as_ref().needs_consolidation.is_some(),
            ) {
                (false, true) => Ordering::Less,
                (true, false) => Ordering::Greater,
                (false, false) | (true, true) => utxo_b.as_ref().value.cmp(&utxo_a.as_ref().value),
            }
        });

        // If consolidation is not enabled, we just sort by value (biggest first)
        #[cfg(not(feature = "utxo-consolidation"))]
        utxo_indices.sort_by(|&a, &b| utxos[b].as_ref().value.cmp(&utxos[a].as_ref().value));

        let mut selected_count = 0;
        for i in 0..utxo_indices.len() {
            if btc_amount >= amount {
                break;
            }

            let utxo_idx = utxo_indices[i];
            let utxo = &utxos[utxo_idx];
            utxo_indices[selected_count] = utxo_idx;
            selected_count += 1;
            btc_amount += self.add_btc_input_for_simple(
                utxo,
                program_info_pubkey,
                &mut consolidation_inputs_count,
                &mut total_consolidation_input_amount,
            )?;
        }

        if btc_amount < amount {
            return Err(BitcoinTxError::NotEnoughBtcInPool);
        }

        #[cfg(feature = "utxo-consolidation")]
        self.set_consolidation_tracking(
            total_consolidation_input_amount,
            crate::input_calc::ARCH_INPUT_SIZE * consolidation_inputs_count as usize,
        );

        utxo_indices.truncate(selected_count);
        Ok((utxo_indices, btc_amount))
    }

    /// Greedily selects UTXOs from holders until at least `amount` satoshis are gathered.
    /// Optionally targets `amount + DUST_LIMIT` with early exit allowed on exact `amount`.
    pub fn find_btc_in_utxos_from_holder<BtcHolder>(
        &mut self,
        holder: &[BtcHolder],
        program_info_pubkey: &Pubkey,
        amount: u64,
        enforce_dust_remainder: bool,
    ) -> Result<u64, BitcoinTxError>
    where
        BtcHolder: BtcUtxoHolder,
    {
        if amount == 0 {
            return Ok(0);
        }

        let mut btc_amount: u64 = 0;

        let mut consolidation_inputs_count: u32 = 0;
        let mut total_consolidation_input_amount: u64 = 0;

        let mut selected_pairs: FixedList<(usize, usize), MAX_INPUTS_TO_SIGN> = FixedList::new();

        let target_amount = if enforce_dust_remainder {
            amount.saturating_add(DUST_LIMIT)
        } else {
            amount
        };

        // Fill to target
        loop {
            // Early exit: if dust remainder enforcement is enabled but we've matched
            // the exact requested amount, do not force an additional input.
            if btc_amount >= target_amount || (enforce_dust_remainder && btc_amount == amount) {
                break;
            }

            let best = self.pick_best_btc_candidate(holder, &selected_pairs);
            let (best_h, best_u) = match best {
                Some(pair) => pair,
                None => return Err(BitcoinTxError::NotEnoughBtcInPool),
            };
            let utxo = &holder[best_h].btc_utxos()[best_u];
            let added = self.add_btc_input_and_track(
                utxo,
                program_info_pubkey,
                &mut selected_pairs,
                (best_h, best_u),
                &mut consolidation_inputs_count,
                &mut total_consolidation_input_amount,
            )?;
            btc_amount = btc_amount.saturating_add(added);
        }

        // Ensure at least one BTC UTXO from each holder is included
        btc_amount = btc_amount.saturating_add(self.minimally_involve_each_holder(
            holder,
            program_info_pubkey,
            &mut selected_pairs,
            &mut consolidation_inputs_count,
            &mut total_consolidation_input_amount,
        )?);

        #[cfg(feature = "utxo-consolidation")]
        self.set_consolidation_tracking(
            total_consolidation_input_amount,
            crate::input_calc::ARCH_INPUT_SIZE * consolidation_inputs_count as usize,
        );

        Ok(btc_amount)
    }

    /// Pick the next best BTC UTXO candidate across all holders that hasn't been selected yet.
    fn pick_best_btc_candidate<BtcHolder: BtcUtxoHolder>(
        &self,
        holder: &[BtcHolder],
        selected_pairs: &FixedList<(usize, usize), MAX_INPUTS_TO_SIGN>,
    ) -> Option<(usize, usize)> {
        let mut best: Option<(usize, usize)> = None;

        #[cfg(feature = "utxo-consolidation")]
        {
            for (h_idx, h) in holder.iter().enumerate() {
                for (u_idx, utxo) in h.btc_utxos().iter().enumerate() {
                    if selected_pairs
                        .iter()
                        .any(|&(h, u)| h == h_idx && u == u_idx)
                    {
                        continue;
                    }

                    match best {
                        None => best = Some((h_idx, u_idx)),
                        Some((bh, bu)) => {
                            let best_utxo = &holder[bh].btc_utxos()[bu];

                            // Prefer UTXOs that do NOT need consolidation. If both equal, pick larger value.
                            let candidate_pref = utxo.needs_consolidation.is_some();
                            let best_pref = best_utxo.needs_consolidation.is_some();

                            if (!candidate_pref && best_pref)
                                || (candidate_pref == best_pref && utxo.value > best_utxo.value)
                            {
                                best = Some((h_idx, u_idx));
                            }
                        }
                    }
                }
            }
        }

        #[cfg(not(feature = "utxo-consolidation"))]
        {
            for (h_idx, h) in holder.iter().enumerate() {
                for (u_idx, utxo) in h.btc_utxos().iter().enumerate() {
                    if selected_pairs
                        .iter()
                        .any(|&(h, u)| h == h_idx && u == u_idx)
                    {
                        continue;
                    }

                    match best {
                        None => best = Some((h_idx, u_idx)),
                        Some((bh, bu)) => {
                            let best_utxo = &holder[bh].btc_utxos()[bu];
                            if utxo.value > best_utxo.value {
                                best = Some((h_idx, u_idx));
                            }
                        }
                    }
                }
            }
        }

        best
    }

    // No clone helper needed; we pass references directly to avoid copies

    /// Add a BTC input and update accounting/selection tracking for holder-based selection.
    fn add_btc_input_and_track<RS>(
        &mut self,
        utxo_ref: &UtxoInfo<RS>,
        program_info_pubkey: &Pubkey,
        selected_pairs: &mut FixedList<(usize, usize), MAX_INPUTS_TO_SIGN>,
        pair: (usize, usize),
        consolidation_inputs_count: &mut u32,
        total_consolidation_input_amount: &mut u64,
    ) -> Result<u64, BitcoinTxError>
    where
        RS: satellite_collections::generic::fixed_set::FixedCapacitySet<
            Item = arch_program::rune::RuneAmount,
        >,
    {
        self.add_tx_input(utxo_ref, &TxStatus::Confirmed, Some(program_info_pubkey))?;

        let added: u64 = utxo_ref.value;

        #[cfg(feature = "utxo-consolidation")]
        {
            if utxo_ref.needs_consolidation.is_some() {
                *consolidation_inputs_count += 1;
                *total_consolidation_input_amount += utxo_ref.value;
            }
        }

        selected_pairs
            .push(pair)
            .map_err(|_| BitcoinTxError::InputToSignListFull)?;

        Ok(added)
    }

    /// Add a BTC input from a simple list and update accounting.
    fn add_btc_input_for_simple<T: AsRef<UtxoInfo<RuneSet>>>(
        &mut self,
        utxo: &T,
        program_info_pubkey: &Pubkey,
        consolidation_inputs_count: &mut u32,
        total_consolidation_input_amount: &mut u64,
    ) -> Result<u64, BitcoinTxError> {
        let utxo_ref = utxo.as_ref();
        self.add_tx_input(utxo_ref, &TxStatus::Confirmed, Some(program_info_pubkey))?;

        #[cfg(feature = "utxo-consolidation")]
        if utxo_ref.needs_consolidation.is_some() {
            *consolidation_inputs_count += 1;
            *total_consolidation_input_amount += utxo_ref.value;
        }

        Ok(utxo_ref.value)
    }

    /// Ensure at least one BTC input was selected from each holder (if they have UTXOs).
    fn minimally_involve_each_holder<BtcHolder: BtcUtxoHolder>(
        &mut self,
        holder: &[BtcHolder],
        program_info_pubkey: &Pubkey,
        selected_pairs: &mut FixedList<(usize, usize), MAX_INPUTS_TO_SIGN>,
        consolidation_inputs_count: &mut u32,
        total_consolidation_input_amount: &mut u64,
    ) -> Result<u64, BitcoinTxError> {
        let mut added_total: u64 = 0;

        for (h_idx, h) in holder.iter().enumerate() {
            if h.btc_utxos().is_empty() {
                continue;
            }

            // Skip if this holder already contributed
            if selected_pairs.iter().any(|&(sh, _)| sh == h_idx) {
                continue;
            }

            // Pick a minimal-impact UTXO index for this holder
            let mut candidate_idx: Option<usize> = None;

            #[cfg(feature = "utxo-consolidation")]
            {
                for (u_idx, utxo) in h.btc_utxos().iter().enumerate() {
                    if utxo.needs_consolidation.is_none() {
                        match candidate_idx {
                            None => candidate_idx = Some(u_idx),
                            Some(ci) => {
                                if utxo.value < h.btc_utxos()[ci].value {
                                    candidate_idx = Some(u_idx);
                                }
                            }
                        }
                    }
                }
                if candidate_idx.is_none() {
                    for (u_idx, utxo) in h.btc_utxos().iter().enumerate() {
                        match candidate_idx {
                            None => candidate_idx = Some(u_idx),
                            Some(ci) => {
                                if utxo.value < h.btc_utxos()[ci].value {
                                    candidate_idx = Some(u_idx);
                                }
                            }
                        }
                    }
                }
            }

            #[cfg(not(feature = "utxo-consolidation"))]
            {
                for (u_idx, utxo) in h.btc_utxos().iter().enumerate() {
                    match candidate_idx {
                        None => candidate_idx = Some(u_idx),
                        Some(ci) => {
                            if utxo.value < h.btc_utxos()[ci].value {
                                candidate_idx = Some(u_idx);
                            }
                        }
                    }
                }
            }

            if let Some(u_idx) = candidate_idx {
                if selected_pairs
                    .iter()
                    .any(|&(sh, su)| sh == h_idx && su == u_idx)
                {
                    continue;
                }

                let utxo = &h.btc_utxos()[u_idx];
                let added = self.add_btc_input_and_track(
                    utxo,
                    program_info_pubkey,
                    selected_pairs,
                    (h_idx, u_idx),
                    consolidation_inputs_count,
                    total_consolidation_input_amount,
                )?;
                added_total = added_total.saturating_add(added);
            }
        }

        Ok(added_total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "utxo-consolidation")]
    use crate::utxo_info::FixedOptionF64;
    use crate::utxo_info::SingleRuneSet;
    #[cfg(feature = "utxo-consolidation")]
    use crate::utxo_info::UtxoInfoTrait;
    use arch_program::pubkey::Pubkey;
    use arch_program::utxo::UtxoMeta;

    fn utxo(value: u64, vout: u32) -> UtxoInfo<SingleRuneSet> {
        UtxoInfo::new(UtxoMeta::from([0; 32], vout), value)
    }

    struct TestHolder {
        utxos: Vec<UtxoInfo<SingleRuneSet>>,
    }

    impl BtcUtxoHolder for TestHolder {
        fn btc_utxos(&self) -> &[UtxoInfo] {
            self.utxos.as_slice()
        }
    }

    const PUBKEY: Pubkey = Pubkey([0; 32]);

    #[test]
    fn list_selection_basic() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let utxos = vec![utxo(5_000, 0), utxo(12_000, 2), utxo(7_000, 1)];
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = utxos.iter().collect();

        let (selected_indices, total) = builder
            .find_btc_in_utxos(&utxo_refs, &PUBKEY, 10_000)
            .unwrap();

        // Greedy by value should pick 12k first, then 5k (or 7k) to surpass 10k
        assert!(total >= 10_000);
        assert!(!selected_indices.is_empty());
        // Ensure inputs were added
        assert_eq!(builder.transaction.input.len(), selected_indices.len());
    }

    #[test]
    fn list_selection_insufficient_errors() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let utxos = vec![utxo(500, 0), utxo(500, 1)];
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = utxos.iter().collect();
        let err = builder
            .find_btc_in_utxos(&utxo_refs, &PUBKEY, 2_000)
            .unwrap_err();
        assert_eq!(err, BitcoinTxError::NotEnoughBtcInPool);
    }

    #[test]
    fn holder_selection_basic() {
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(5_000, 0)],
            },
            TestHolder {
                utxos: vec![utxo(12_000, 1)],
            },
        ];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let amount = 10_000;

        let total = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, amount, false)
            .unwrap();

        assert_eq!(total, 17_000);
        // Should have at least one input (and ≤ number of UTXOs)
        assert!(builder.transaction.input.len() >= 1);
    }

    #[test]
    fn holder_selection_dust_enforcement_adds_input() {
        // Pick 2000 first for amount 1600 → remainder 400 (< 546), enforcement should add 600
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(2_000, 0)],
            },
            TestHolder {
                utxos: vec![utxo(600, 1)],
            },
        ];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let amount = 1_600;

        let total = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, amount, true)
            .unwrap();

        assert_eq!(total, 2_600);
        let remainder = total - amount;
        assert!(remainder == 0 || remainder >= DUST_LIMIT);
    }

    #[test]
    fn holder_selection_dust_enforcement_exact_match_allows_early_exit() {
        let holders = vec![TestHolder {
            utxos: vec![utxo(1_600, 0)],
        }];
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let amount = 1_600;

        let total = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, amount, true)
            .unwrap();

        assert_eq!(total, amount);
    }

    #[test]
    fn holder_selection_dust_enforcement_remainder_ge_dust_no_extra_input() {
        // Single holder where the first pick yields amount + DUST_LIMIT exactly.
        // With enforce_dust = true, this should not add any extra inputs.
        let holders = vec![TestHolder {
            utxos: vec![utxo(1_000 + DUST_LIMIT, 0), utxo(10_000, 1)],
        }];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let amount = 1_000;

        let total = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, amount, true)
            .unwrap();

        // Greedy selection picks the largest UTXO first; ensure we don't add an extra input
        // when the remainder is already >= DUST_LIMIT.
        assert!(total >= amount);
        assert_eq!(builder.transaction.input.len(), 1);
        let remainder = total - amount;
        assert!(remainder == 0 || remainder >= DUST_LIMIT);
    }

    #[test]
    fn holder_selection_dust_enforcement_exact_match_across_multiple_utxos() {
        // Exact amount achieved by summing multiple UTXOs from a single holder.
        // enforce_dust = true should allow early exit once btc_amount == amount.
        let holders = vec![TestHolder {
            utxos: vec![utxo(900, 0), utxo(700, 1)],
        }];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let amount = 1_600;

        let total = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, amount, true)
            .unwrap();

        assert_eq!(total, amount);
        assert_eq!(builder.transaction.input.len(), 2);
    }

    #[test]
    fn holder_selection_saturating_add_target_overflow_not_enough_pool() {
        // Use a very large requested amount that would saturate when adding DUST_LIMIT.
        // Provide UTXOs that cannot reach the saturated target to ensure we error out.
        let holders = vec![TestHolder {
            utxos: vec![UtxoInfo::new(UtxoMeta::from([0; 32], 0), u64::MAX - 2)],
        }];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let amount = u64::MAX - DUST_LIMIT + 1; // target_amount will saturate to u64::MAX

        let err = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, amount, true)
            .unwrap_err();

        assert_eq!(err, BitcoinTxError::NotEnoughBtcInPool);
    }

    #[test]
    fn list_selection_zero_amount_returns_empty_and_no_inputs() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let utxos = vec![utxo(5_000, 0), utxo(7_000, 1)];
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = utxos.iter().collect();

        let (indices, total) = builder.find_btc_in_utxos(&utxo_refs, &PUBKEY, 0).unwrap();

        assert_eq!(indices.len(), 0);
        assert_eq!(total, 0);
        assert_eq!(builder.transaction.input.len(), 0);
    }

    #[test]
    fn holder_selection_zero_amount_returns_zero_and_no_inputs() {
        let holders = vec![TestHolder {
            utxos: vec![utxo(5_000, 0)],
        }];
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();

        let total = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, 0, false)
            .unwrap();

        assert_eq!(total, 0);
        assert_eq!(builder.transaction.input.len(), 0);
    }

    #[test]
    fn list_selection_empty_pool_errors() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = vec![];
        let err = builder
            .find_btc_in_utxos(&utxo_refs, &PUBKEY, 1_000)
            .unwrap_err();
        assert_eq!(err, BitcoinTxError::NotEnoughBtcInPool);
    }

    #[test]
    fn holder_selection_empty_holders_errors() {
        let holders: Vec<TestHolder> = vec![];
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let err = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, 1_000, false)
            .unwrap_err();
        assert_eq!(err, BitcoinTxError::NotEnoughBtcInPool);
    }

    #[test]
    fn list_selection_returns_correct_original_indices_for_multiple_picks() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        // Values: [5k (idx 0), 12k (idx 1), 7k (idx 2)]
        let utxos = vec![utxo(5_000, 0), utxo(12_000, 1), utxo(7_000, 2)];
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = utxos.iter().collect();

        // Need more than 12k to force picking 12k + 7k
        let (indices, total) = builder
            .find_btc_in_utxos(&utxo_refs, &PUBKEY, 18_000)
            .unwrap();

        assert_eq!(indices.len(), 2);
        assert!(indices.contains(&1)); // 12k
        assert!(indices.contains(&2)); // 7k
        assert_eq!(total, 19_000);
    }

    #[test]
    fn minimally_involve_each_holder_adds_one_from_each_remaining_holder() {
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(700, 0)],
            },
            TestHolder {
                utxos: vec![utxo(2_000, 0)],
            },
            TestHolder {
                utxos: vec![utxo(300, 0)],
            },
        ];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let mut selected_pairs: FixedList<(usize, usize), 4> = FixedList::new();

        // Simulate that holder 1 already contributed its only UTXO
        selected_pairs.push((1, 0)).unwrap();

        let mut cons_inputs = 0u32;
        let mut cons_amount = 0u64;

        let added = builder
            .minimally_involve_each_holder(
                &holders,
                &PUBKEY,
                &mut selected_pairs,
                &mut cons_inputs,
                &mut cons_amount,
            )
            .unwrap();

        // Should add 700 + 300 (smallest from remaining holders)
        assert_eq!(added, 1_000);
        // Transaction should now have 2 inputs corresponding to those additions
        assert_eq!(builder.transaction.input.len(), 2);
    }

    #[test]
    fn add_btc_input_for_simple_adds_input_and_returns_value() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let u = utxo(9_999, 0);
        let mut cons_inputs = 0u32;
        let mut cons_amount = 0u64;
        let added = builder
            .add_btc_input_for_simple(&u, &PUBKEY, &mut cons_inputs, &mut cons_amount)
            .unwrap();
        assert_eq!(added, 9_999);
        assert_eq!(builder.transaction.input.len(), 1);
    }

    #[test]
    fn add_btc_input_and_track_updates_selection_and_returns_value() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();

        // Use a UTXO with the correct internal generic type directly
        let utxo_clone = utxo(4_200, 0);

        let mut selected_pairs: FixedList<(usize, usize), 4> = FixedList::new();
        let mut cons_inputs = 0u32;
        let mut cons_amount = 0u64;

        let added = builder
            .add_btc_input_and_track(
                &utxo_clone,
                &PUBKEY,
                &mut selected_pairs,
                (0, 0),
                &mut cons_inputs,
                &mut cons_amount,
            )
            .unwrap();

        assert_eq!(added, 4_200);
        assert_eq!(builder.transaction.input.len(), 1);
        assert_eq!(selected_pairs.len(), 1);
    }

    #[test]
    #[cfg(not(feature = "utxo-consolidation"))]
    fn pick_best_btc_candidate_prefers_larger_value_without_consolidation() {
        let builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(3_000, 0), utxo(5_000, 1)],
            },
            TestHolder {
                utxos: vec![utxo(10_000, 0)],
            },
        ];
        let selected: FixedList<(usize, usize), 4> = FixedList::new();

        let best = builder
            .pick_best_btc_candidate(&holders, &selected)
            .unwrap();
        // Should be the 10k from holder 1
        assert_eq!(best, (1, 0));
    }

    #[test]
    #[cfg(feature = "utxo-consolidation")]
    fn pick_best_btc_candidate_prefers_non_consolidation_then_value() {
        let builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();

        fn cons(value: u64, vout: u32) -> UtxoInfo<SingleRuneSet> {
            let mut u = UtxoInfo::new(UtxoMeta::from([0; 32], vout), value);
            *u.needs_consolidation_mut() = FixedOptionF64::some(1.0);
            u
        }

        let holders = vec![
            TestHolder {
                utxos: vec![cons(8_000, 0), utxo(7_000, 1)],
            }, // prefers 7k (non-cons) over 8k (cons)
            TestHolder {
                utxos: vec![cons(12_000, 0)],
            },
        ];

        let selected: FixedList<(usize, usize), 4> = FixedList::new();
        let best = builder
            .pick_best_btc_candidate(&holders, &selected)
            .unwrap();
        assert_eq!(best, (0, 1)); // the 7k non-consolidation utxo
    }

    #[test]
    fn minimally_involve_each_holder_skips_already_contributed_holders() {
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(1_000, 0)],
            },
            TestHolder {
                utxos: vec![utxo(2_000, 0)],
            },
        ];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let mut selected_pairs: FixedList<(usize, usize), 4> = FixedList::new();
        // Mark both holders as already contributing
        selected_pairs.push((0, 0)).unwrap();
        selected_pairs.push((1, 0)).unwrap();

        let mut cons_inputs = 0u32;
        let mut cons_amount = 0u64;
        let added = builder
            .minimally_involve_each_holder(
                &holders,
                &PUBKEY,
                &mut selected_pairs,
                &mut cons_inputs,
                &mut cons_amount,
            )
            .unwrap();

        // No additional inputs should be added
        assert_eq!(added, 0);
        assert_eq!(builder.transaction.input.len(), 0);
    }

    #[test]
    fn holder_selection_errors_when_input_to_sign_capacity_exceeded() {
        // Need at least 2 inputs to reach amount but MAX_INPUTS_TO_SIGN is 1 → should error
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(500, 0)],
            },
            TestHolder {
                utxos: vec![utxo(600, 0)],
            },
        ];

        let mut builder: TransactionBuilder<8, 1, SingleRuneSet> = TransactionBuilder::new();
        let err = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, 1_000, false)
            .unwrap_err();

        assert_eq!(err, BitcoinTxError::InputToSignListFull);
    }

    #[test]
    fn list_selection_exact_match_single() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let utxos = vec![utxo(1_000, 0), utxo(2_000, 1), utxo(12_000, 2)];
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = utxos.iter().collect();

        let (indices, total) = builder
            .find_btc_in_utxos(&utxo_refs, &PUBKEY, 12_000)
            .unwrap();

        assert_eq!(total, 12_000);
        assert_eq!(indices, vec![2]);
        assert_eq!(builder.transaction.input.len(), 1);
    }

    #[test]
    fn list_selection_errors_when_input_to_sign_capacity_exceeded() {
        // Need at least 2 inputs to reach amount but MAX_INPUTS_TO_SIGN is 1 → should error
        let mut builder: TransactionBuilder<8, 1, SingleRuneSet> = TransactionBuilder::new();
        let utxos = vec![utxo(500, 0), utxo(600, 1)];
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = utxos.iter().collect();

        let err = builder
            .find_btc_in_utxos(&utxo_refs, &PUBKEY, 1_000)
            .unwrap_err();

        assert_eq!(err, BitcoinTxError::InputToSignListFull);
    }

    #[test]
    fn pick_best_btc_candidate_returns_none_when_all_selected() {
        let builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(1_000, 0)],
            },
            TestHolder {
                utxos: vec![utxo(2_000, 0)],
            },
        ];

        let mut selected: FixedList<(usize, usize), 4> = FixedList::new();
        selected.push((0, 0)).unwrap();
        selected.push((1, 0)).unwrap();

        let best = builder.pick_best_btc_candidate(&holders, &selected);
        assert!(best.is_none());
    }

    #[test]
    fn pick_best_btc_candidate_skips_already_selected_and_picks_next_best() {
        let builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let holders = vec![
            TestHolder {
                utxos: vec![utxo(5_000, 0)],
            },
            TestHolder {
                utxos: vec![utxo(4_000, 0), utxo(3_000, 1)],
            },
        ];

        let mut selected: FixedList<(usize, usize), 4> = FixedList::new();
        // Mark the best overall candidate (holder 0, utxo 0) as already selected
        selected.push((0, 0)).unwrap();

        let best = builder.pick_best_btc_candidate(&holders, &selected).unwrap();
        // Should now pick the next best, which is holder 1's 4k utxo
        assert_eq!(best, (1, 0));
    }

    #[test]
    fn minimally_involve_each_holder_skips_empty_holders() {
        let holders = vec![
            TestHolder { utxos: vec![] },
            TestHolder {
                utxos: vec![utxo(700, 0)],
            },
            TestHolder { utxos: vec![] },
        ];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let mut selected_pairs: FixedList<(usize, usize), 4> = FixedList::new();

        let mut cons_inputs = 0u32;
        let mut cons_amount = 0u64;

        let added = builder
            .minimally_involve_each_holder(
                &holders,
                &PUBKEY,
                &mut selected_pairs,
                &mut cons_inputs,
                &mut cons_amount,
            )
            .unwrap();

        assert_eq!(added, 700);
        assert_eq!(builder.transaction.input.len(), 1);
    }

    #[test]
    fn minimally_involve_each_holder_errors_when_selection_capacity_full() {
        // selected_pairs is full; attempting to minimally involve another holder should error
        let holders = vec![
            TestHolder { utxos: vec![utxo(700, 0)] },
            TestHolder { utxos: vec![utxo(800, 0)] },
        ];

        let mut builder: TransactionBuilder<8, 1, SingleRuneSet> = TransactionBuilder::new();
        let mut selected_pairs: FixedList<(usize, usize), 1> = FixedList::new();
        selected_pairs.push((0, 0)).unwrap(); // capacity reached

        let mut cons_inputs = 0u32;
        let mut cons_amount = 0u64;

        let err = builder
            .minimally_involve_each_holder(
                &holders,
                &PUBKEY,
                &mut selected_pairs,
                &mut cons_inputs,
                &mut cons_amount,
            )
            .unwrap_err();

        assert_eq!(err, BitcoinTxError::InputToSignListFull);
    }

    #[test]
    #[cfg(feature = "utxo-consolidation")]
    fn minimally_involve_prefers_non_consolidation_smallest() {
        // Each holder has a consolidation-marked small UTXO and a larger non-consolidation UTXO.
        // The minimal involvement should pick the smallest non-consolidation UTXO per holder.
        fn cons(value: u64, vout: u32) -> UtxoInfo<SingleRuneSet> {
            let mut u = UtxoInfo::new(UtxoMeta::from([0; 32], vout), value);
            *u.needs_consolidation_mut() = FixedOptionF64::some(1.0);
            u
        }

        let holders = vec![
            TestHolder {
                utxos: vec![cons(100, 0), utxo(1_000, 1)],
            },
            TestHolder {
                utxos: vec![cons(200, 0), utxo(500, 1)],
            },
        ];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        let mut selected_pairs: FixedList<(usize, usize), 4> = FixedList::new();

        let mut cons_inputs = 0u32;
        let mut cons_amount = 0u64;

        let added = builder
            .minimally_involve_each_holder(
                &holders,
                &PUBKEY,
                &mut selected_pairs,
                &mut cons_inputs,
                &mut cons_amount,
            )
            .unwrap();

        assert_eq!(added, 1_500);
        assert!(selected_pairs
            .iter()
            .any(|&(h, u)| h == 0 && u == 1));
        assert!(selected_pairs
            .iter()
            .any(|&(h, u)| h == 1 && u == 1));
    }

    #[test]
    #[cfg(feature = "utxo-consolidation")]
    fn list_selection_prefers_non_consolidation_then_value() {
        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();

        fn cons(value: u64, vout: u32) -> UtxoInfo<SingleRuneSet> {
            let mut u = UtxoInfo::new(UtxoMeta::from([0; 32], vout), value);
            *u.needs_consolidation_mut() = FixedOptionF64::some(1.0);
            u
        }

        // Prefer the 7k non-consolidation UTXO over larger consolidation UTXOs
        let utxos = vec![cons(8_000, 0), utxo(7_000, 1), cons(12_000, 2)];
        let utxo_refs: Vec<&UtxoInfo<SingleRuneSet>> = utxos.iter().collect();

        let (indices, total) = builder
            .find_btc_in_utxos(&utxo_refs, &PUBKEY, 7_000)
            .unwrap();

        assert_eq!(total, 7_000);
        assert_eq!(indices, vec![1]);
        assert_eq!(builder.transaction.input.len(), 1);
    }

    #[test]
    #[cfg(feature = "utxo-consolidation")]
    fn holder_selection_sets_consolidation_tracking() {
        use crate::input_calc::ARCH_INPUT_SIZE;

        let holders = vec![
            TestHolder {
                utxos: vec![
                    // both need consolidation
                    {
                        let mut u = UtxoInfo::new(UtxoMeta::from([0; 32], 0), 2_000);
                        *u.needs_consolidation_mut() = FixedOptionF64::some(1.0);
                        u
                    },
                    {
                        let mut u = UtxoInfo::new(UtxoMeta::from([0; 32], 1), 3_000);
                        *u.needs_consolidation_mut() = FixedOptionF64::some(1.0);
                        u
                    },
                ],
            },
            TestHolder {
                utxos: vec![utxo(4_000, 0)], // non-consolidation
            },
        ];

        let mut builder: TransactionBuilder<8, 4, SingleRuneSet> = TransactionBuilder::new();
        // Require more than 4k so we also pick one consolidation UTXO
        let total = builder
            .find_btc_in_utxos_from_holder(&holders, &PUBKEY, 6_000, false)
            .unwrap();

        assert!(total >= 7_000);
        // Should have counted exactly one consolidation input (the 3k preferred over 2k)
        assert_eq!(builder.total_btc_consolidation_input, 3_000);
        assert_eq!(builder.extra_tx_size_for_consolidation, ARCH_INPUT_SIZE);
    }
}
