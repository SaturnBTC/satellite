use arch_program::{account::AccountInfo, program::get_account_script_pubkey};
use bitcoin::Transaction;
use satellite_collections::generic::fixed_list::{FixedList, FixedListError};

/// Get the used shards in a transaction.
///
/// This function will reorder the accounts in the transaction to match the order of the accounts in the accounts list.
///
/// # Arguments
///
/// * `transaction` - The transaction to get the used shards from.
/// * `accounts` - The accounts to get the used shards from.
///
/// # Returns
///
/// A list of the used shards in the transaction.
///
/// # Example
///
/// ```ignore
/// use satellite_bitcoin_transactions::util::get_used_shards_in_transaction;
/// use satellite_collections::generic::fixed_list::FixedList;
/// use arch_program::account::AccountInfo;
/// use bitcoin::{Transaction, transaction::Version, absolute::LockTime};
///
/// // Minimal empty transaction for demonstration purposes
/// # let transaction = Transaction {
/// #     version: Version::TWO,
/// #     lock_time: LockTime::ZERO,
/// #     input: vec![],
/// #     output: vec![],
/// # };
/// # // No accounts in this simple example
/// # let accounts: Vec<AccountInfo> = Vec::new();
/// let used_shards: FixedList<usize, 10> =
///     get_used_shards_in_transaction::<10>(&transaction, &accounts);
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

pub fn reorder_accounts_in_transaction<'a, const SIZE: usize>(
    transaction: &Transaction,
    account_indexes: &mut FixedList<usize, SIZE>,
    accounts: &[AccountInfo<'a>],
) -> Result<(), FixedListError> {
    let mut reordered_account_indexes = FixedList::<usize, SIZE>::new();

    // Iterate over transaction outputs and find matching accounts
    for output in &transaction.output {
        for account_index in account_indexes.iter() {
            if *account_index >= accounts.len() {
                continue;
            }

            let account = &accounts[*account_index];
            let account_script_pubkey = get_account_script_pubkey(&account.key);

            // Compare script pubkeys directly without allocating ScriptBuf
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
    fn reorder_multiple_accounts_all_zero_scripts_selects_first_each_time() {
        // Given the stubbed script pubkey (all zeros), each output matches the first index in `indexes`.
        let tx = tx_with_outputs(vec![vec![0u8; 34], vec![0u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(3));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();
        indexes.push(1).unwrap();
        indexes.push(2).unwrap();

        reorder_accounts_in_transaction(&tx, &mut indexes, &accounts).unwrap();
        assert_eq!(indexes.as_slice(), &[0, 0, 0]);
    }

    #[test]
    fn reorder_out_of_bounds_indices_are_ignored_if_a_valid_match_exists() {
        // account indices [5,1] with 2 outputs -> both will match index 1 (first valid).
        let tx = tx_with_outputs(vec![vec![0u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(2));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(5).unwrap();
        indexes.push(1).unwrap();

        reorder_accounts_in_transaction(&tx, &mut indexes, &accounts).unwrap();
        assert_eq!(indexes.as_slice(), &[1, 1]);
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
    #[should_panic(expected = "All accounts must be matched")]
    fn reorder_panics_when_more_outputs_than_indexes() {
        // 2 outputs but only 1 index -> will push twice, then len != indexes.len().
        let tx = tx_with_outputs(vec![vec![0u8; 34], vec![0u8; 34]]);
        let accounts = leak_accounts_slice(make_accounts(1));
        let mut indexes: FixedList<usize, 4> = FixedList::new();
        indexes.push(0).unwrap();

        let _ = reorder_accounts_in_transaction(&tx, &mut indexes, &accounts);
    }
}
