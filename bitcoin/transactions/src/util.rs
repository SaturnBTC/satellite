use arch_program::{account::AccountInfo, program::get_account_script_pubkey};
use bitcoin::Transaction;
use satellite_collections::generic::fixed_list::{FixedList, FixedListError};

/// Get the indexes of writable accounts ("used shards").
///
/// Scans `accounts` and returns a fixed-capacity list of indexes for all
/// accounts marked as writable.
///
/// # Returns
///
/// A list of account indexes that are writable.
///
/// # Example
///
/// ```ignore
/// use satellite_bitcoin_transactions::util::get_used_shards_in_transaction;
/// use satellite_collections::generic::fixed_list::FixedList;
/// use arch_program::account::AccountInfo;
///
/// # let accounts: Vec<AccountInfo> = Vec::new();
/// let used_shards: FixedList<usize, 10> = get_used_shards_in_transaction::<10>(&accounts);
/// # assert!(used_shards.is_empty());
/// ```
pub fn get_used_shards_in_transaction<'a, const SIZE: usize>(
    accounts: &'a [AccountInfo<'a>],
) -> Result<FixedList<usize, SIZE>, FixedListError> {
    let mut used_shards = FixedList::<usize, SIZE>::new();

    for (index, account) in accounts.iter().enumerate() {
        if account.is_writable {
            used_shards.push(index)?;
        }
    }

    Ok(used_shards)
}

/// Reorder `account_indexes` to follow the output order in `transaction`.
///
/// For every index in `account_indexes`, the corresponding `accounts[index]` is
/// converted to a script pubkey and compared against the outputs of `transaction`.
/// On success, `account_indexes` is overwritten in place with the same indices
/// reordered to reflect the order in which their scripts appear in the outputs.
///
/// # Errors
///
/// Returns a [`FixedListError::Full`] if the internal scratch list exceeds
/// capacity (should not occur when capacities are consistent).
///
/// # Panics
///
/// Panics with "All accounts must be matched" if any index is out of bounds for
/// `accounts` or if no matching output is found in `transaction` for any index.
///
/// # Arguments
///
/// - `transaction`: The Bitcoin transaction whose outputs are scanned.
/// - `account_indexes`: In/out list of account indices to validate.
/// - `accounts`: The account slice providing the keys used to derive script pubkeys.
///
/// # Example
///
/// ```ignore
/// use satellite_collections::generic::fixed_list::FixedList;
/// use bitcoin::{Transaction, absolute::LockTime, transaction::Version};
///
/// # let tx = Transaction { version: Version::TWO, lock_time: LockTime::ZERO, input: vec![], output: vec![] };
/// # let accounts: &[arch_program::account::AccountInfo] = &[];
/// let mut idx: FixedList<usize, 4> = FixedList::new();
/// let _ = reorder_accounts_in_transaction(&tx, &mut idx, accounts);
/// ```
pub fn reorder_accounts_in_transaction<'a, const SIZE: usize>(
    transaction: &Transaction,
    account_indexes: &mut FixedList<usize, SIZE>,
    accounts: &[AccountInfo<'a>],
) -> Result<(), FixedListError> {
    let mut reordered_account_indexes = FixedList::<usize, SIZE>::new();

    for output in &transaction.output {
        if reordered_account_indexes.len() == account_indexes.len() {
            break;
        }

        for account_index in account_indexes.iter() {
            if *account_index >= accounts.len() {
                continue;
            }

            if reordered_account_indexes.contains(account_index) {
                continue;
            }

            let account = &accounts[*account_index];
            let account_script_pubkey = get_account_script_pubkey(&account.key);

            if output.script_pubkey.as_bytes() == account_script_pubkey {
                reordered_account_indexes.push(*account_index)?;
                break;
            }
        }
    }

    assert_eq!(
        reordered_account_indexes.len(),
        account_indexes.len(),
        "All accounts must be matched"
    );

    // Replace the original account_indexes with the reordered list
    account_indexes.copy_from_slice(reordered_account_indexes.as_slice());

    Ok(())
}

/// Return the output positions that match the provided `account_indexes`.
///
/// This is a generic helper that scans the transaction outputs and, for each
/// output, finds the first matching account (by script pubkey) among the
/// provided `account_indexes`. It returns the list of output indices (0-based)
/// that correspond to the matched accounts, preserving the output order.
///
/// Invariants:
/// - Every matched output corresponds to exactly one of the provided indexes.
/// - The number of matched outputs must equal the number of provided indexes.
pub fn match_account_indexes_to_output_positions<'a, const SIZE: usize>(
    transaction: &Transaction,
    account_indexes: &FixedList<usize, SIZE>,
    accounts: &[AccountInfo<'a>],
) -> Result<(FixedList<usize, SIZE>, FixedList<usize, SIZE>), FixedListError> {
    let mut matched_account_indexes = FixedList::<usize, SIZE>::new();
    let mut matched_output_positions = FixedList::<usize, SIZE>::new();

    for (output_position, output) in transaction.output.iter().enumerate() {
        if matched_account_indexes.len() == account_indexes.len() {
            break;
        }

        for account_index in account_indexes.iter() {
            if *account_index >= accounts.len() {
                continue;
            }

            if matched_account_indexes.contains(account_index) {
                continue;
            }

            let account = &accounts[*account_index];
            let account_script_pubkey = get_account_script_pubkey(&account.key);

            if output.script_pubkey.as_bytes() == account_script_pubkey {
                matched_account_indexes.push(*account_index)?;
                matched_output_positions.push(output_position)?;
                break;
            }
        }
    }

    assert_eq!(
        matched_account_indexes.len(),
        account_indexes.len(),
        "All accounts must be matched",
    );

    Ok((matched_account_indexes, matched_output_positions))
}

/// Assert that a given `account` appears as the script at `output_index`.
///
/// This utility performs a single script comparison and returns `Ok(())` on
/// match, or an error via the provided `on_mismatch` closure.
pub fn assert_account_is_at_index<'a, E>(
    transaction: &Transaction,
    account: &AccountInfo<'a>,
    output_index: usize,
    on_mismatch: impl FnOnce() -> E,
) -> Result<(), E> {
    if transaction.output.len() <= output_index {
        return Err(on_mismatch());
    }
    let spk = get_account_script_pubkey(&account.key);
    if transaction.output[output_index].script_pubkey.as_bytes() != spk {
        return Err(on_mismatch());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use arch_program::{pubkey::Pubkey, utxo::UtxoMeta};
    use bitcoin::{absolute::LockTime, transaction::Version, ScriptBuf, TxOut};

    fn empty_tx() -> Transaction {
        Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![],
            output: vec![],
        }
    }

    fn tx_with_outputs(script_templates: Vec<Vec<u8>>) -> Transaction {
        let mut tx = empty_tx();
        for bytes in script_templates {
            tx.output.push(TxOut {
                value: bitcoin::Amount::from_sat(0),
                script_pubkey: ScriptBuf::from_bytes(bytes),
            });
        }
        tx
    }

    fn make_accounts(count: usize) -> Vec<AccountInfo<'static>> {
        // Helper to construct `count` accounts with stable backing storage by leaking small boxes.
        let owner_static: &'static Pubkey = Box::leak(Box::new(Pubkey::new_unique()));
        let utxo_static: &'static UtxoMeta = Box::leak(Box::new(UtxoMeta::default()));

        let mut accounts: Vec<AccountInfo<'static>> = Vec::with_capacity(count);
        for _ in 0..count {
            let key: &'static Pubkey = Box::leak(Box::new(Pubkey::new_unique()));
            let lamports_ref: &'static mut u64 = Box::leak(Box::new(0u64));
            let data_ref: &'static mut [u8] = Box::leak(Vec::<u8>::new().into_boxed_slice());
            let account = AccountInfo::new(
                key,
                lamports_ref,
                data_ref,
                owner_static,
                utxo_static,
                /*is_signer=*/ false,
                /*is_writable=*/ true,
                /*is_executable=*/ false,
            );
            accounts.push(account);
        }

        accounts
    }

    fn leak_accounts_slice(accounts: Vec<AccountInfo<'static>>) -> &'static [AccountInfo<'static>] {
        Box::leak(accounts.into_boxed_slice())
    }

    #[test]
    fn reorder_empty_accounts_and_outputs_ok() {
        let tx = empty_tx();
        let accounts = leak_accounts_slice(make_accounts(0));
        let mut indexes: FixedList<usize, 4> = FixedList::new();

        let result = reorder_accounts_in_transaction(&tx, &mut indexes, &accounts);
        assert!(result.is_ok());
        assert_eq!(indexes.len(), 0);
    }

    #[test]
    fn reorder_single_account_single_output_matches_ok() {
        // With non-Solana build, get_account_script_pubkey returns zeros -> use zero script.
        let tx = tx_with_outputs(vec![vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        reorder_accounts_in_transaction(&tx, &mut indexes, &accounts).unwrap();
        assert_eq!(indexes.as_slice(), &[0]);
    }

    #[test]
    #[should_panic(expected = "All accounts must be matched")]
    fn reorder_panics_on_duplicate_indices() {
        // Duplicate indices lead to fewer unique matches than provided indexes,
        // triggering the final assertion.
        let tx = tx_with_outputs(vec![vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();
        indexes.push(0).unwrap();
        let _ = reorder_accounts_in_transaction(&tx, &mut indexes, &accounts);
    }

    #[test]
    fn reorder_multiple_accounts_all_zero_scripts_selects_first_each_time() {
        // With all-zero scripts, each distinct account index still maps to a match.
        // The function preserves the set of unique indices in insertion order.
        let tx = tx_with_outputs(vec![vec![0u8; 34], vec![0u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(3));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();
        indexes.push(1).unwrap();
        indexes.push(2).unwrap();

        reorder_accounts_in_transaction(&tx, &mut indexes, &accounts).unwrap();
        assert_eq!(indexes.as_slice(), &[0, 1, 2]);
    }

    #[test]
    #[should_panic(expected = "All accounts must be matched")]
    fn reorder_panics_when_any_index_is_out_of_bounds() {
        // One index is out of bounds, so not all accounts can be matched.
        let tx = tx_with_outputs(vec![vec![0u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(2));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(5).unwrap();
        indexes.push(1).unwrap();

        let _ = reorder_accounts_in_transaction(&tx, &mut indexes, &accounts).unwrap();
    }

    #[test]
    #[should_panic(expected = "All accounts must be matched")]
    fn reorder_panics_when_no_outputs_for_non_empty_indexes() {
        let tx = empty_tx();
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        let _ = reorder_accounts_in_transaction(&tx, &mut indexes, &accounts);
    }

    #[test]
    #[should_panic(expected = "All accounts must be matched")]
    fn reorder_panics_when_outputs_do_not_match_any_account_script() {
        // Non-zero script won't match stubbed script (zeros), so nothing gets pushed.
        let tx = tx_with_outputs(vec![vec![1u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        let _ = reorder_accounts_in_transaction(&tx, &mut indexes, &accounts);
    }

    #[test]
    fn reorder_ok_when_more_outputs_than_indexes() {
        // Extra outputs do not affect matching; we only match per provided index.
        let tx = tx_with_outputs(vec![vec![0u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        reorder_accounts_in_transaction(&tx, &mut indexes, &accounts).unwrap();
        assert_eq!(indexes.as_slice(), &[0]);
    }

    // =========================
    // match_account_indexes_to_output_positions tests
    // =========================

    #[test]
    fn match_positions_empty_ok() {
        let tx = empty_tx();
        let accounts = leak_accounts_slice(make_accounts(0));
        let indexes: FixedList<usize, 4> = FixedList::new();

        let (matched_indexes, matched_positions) =
            match_account_indexes_to_output_positions(&tx, &indexes, &accounts).unwrap();
        assert_eq!(matched_indexes.len(), 0);
        assert_eq!(matched_positions.len(), 0);
    }

    #[test]
    fn match_positions_single_index_single_output_ok() {
        let tx = tx_with_outputs(vec![vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        let (matched_indexes, matched_positions) =
            match_account_indexes_to_output_positions(&tx, &indexes, &accounts).unwrap();
        assert_eq!(matched_indexes.len(), 1);
        assert_eq!(matched_positions.len(), 1);
        assert!(matched_indexes.contains(&0));
        assert!(matched_positions.contains(&0));
    }

    #[test]
    #[should_panic(expected = "All accounts must be matched")]
    fn match_positions_panics_when_no_outputs() {
        let tx = empty_tx();
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        let _ = match_account_indexes_to_output_positions(&tx, &indexes, &accounts).unwrap();
    }

    #[test]
    #[should_panic(expected = "All accounts must be matched")]
    fn match_positions_panics_when_outputs_do_not_match() {
        let tx = tx_with_outputs(vec![vec![1u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        let _ = match_account_indexes_to_output_positions(&tx, &indexes, &accounts).unwrap();
    }

    #[test]
    fn match_positions_ok_with_identical_output_scripts() {
        // Two outputs have identical scripts; each index should match the first available
        // output in order, yielding output positions [0, 1].
        let tx = tx_with_outputs(vec![vec![0u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(2));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();
        indexes.push(1).unwrap();

        let (matched_indexes, matched_positions) =
            match_account_indexes_to_output_positions(&tx, &indexes, &accounts).unwrap();
        assert_eq!(matched_indexes.as_slice(), &[0, 1]);
        assert_eq!(matched_positions.as_slice(), &[0, 1]);
    }

    #[test]
    #[should_panic(expected = "All accounts must be matched")]
    fn match_positions_panics_on_out_of_bounds_index() {
        let tx = tx_with_outputs(vec![vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(5).unwrap(); // out of bounds

        let _ = match_account_indexes_to_output_positions(&tx, &indexes, &accounts).unwrap();
    }

    // =========================
    // assert_account_is_at_index tests
    // =========================

    #[test]
    fn assert_is_at_index_ok_on_match() {
        let tx = tx_with_outputs(vec![vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));

        let res: Result<(), ()> = assert_account_is_at_index(&tx, &accounts[0], 0, || ());
        assert!(res.is_ok());
    }

    #[test]
    fn assert_is_at_index_err_on_mismatch() {
        let tx = tx_with_outputs(vec![vec![1u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));

        #[derive(Debug, PartialEq)]
        enum MyErr {
            Mismatch,
        }

        let res = assert_account_is_at_index(&tx, &accounts[0], 0, || MyErr::Mismatch);
        assert_eq!(res, Err(MyErr::Mismatch));
    }

    #[test]
    fn assert_is_at_index_err_on_out_of_bounds() {
        let tx = empty_tx();
        let accounts = leak_accounts_slice(make_accounts(1));

        let res: Result<(), &'static str> =
            assert_account_is_at_index(&tx, &accounts[0], 0, || "oob");
        assert_eq!(res, Err("oob"));
    }

    #[test]
    fn assert_is_at_index_ok_on_nonzero_index() {
        // Second output matches zeroed script; should succeed when checking index 1
        let tx = tx_with_outputs(vec![vec![1u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));

        let res: Result<(), ()> = assert_account_is_at_index(&tx, &accounts[0], 1, || ());
        assert!(res.is_ok());
    }
}
