use std::cmp::min;

use crate::mempool::MempoolInfo;
use arch_program::{input_to_sign::InputToSign, msg};
use bitcoin::{Amount, ScriptBuf, Transaction, TxOut, Weight};
use satellite_collections::generic::push_pop::{PushPopCollection, PushPopError};
use satellite_math::{safe_add, safe_sub};

use crate::{
    constants::DUST_LIMIT,
    error::BitcoinTxError,
    fee_rate::FeeRate,
    input_calc::{WITNESS_OVERHEAD_BYTES, WITNESS_OVERHEAD_WU, WITNESS_WEIGHT_BYTES},
    NewPotentialInputAmount, NewPotentialInputsAndOutputs, NewPotentialOutputAmount,
};

#[inline]
fn inputs_to_sign_and_has_witness(transaction: &Transaction) -> (usize, bool) {
    let mut inputs_to_sign = 0usize;
    let mut has_existing_witness = false;
    for txin in transaction.input.iter() {
        if txin.witness.is_empty() {
            inputs_to_sign += 1;
        } else {
            has_existing_witness = true;
        }
    }
    (inputs_to_sign, has_existing_witness)
}

pub(crate) fn estimate_final_tx_total_size(transaction: &Transaction) -> usize {
    let size = transaction.total_size();
    let (inputs_to_sign, has_existing_witness) = inputs_to_sign_and_has_witness(transaction);

    if inputs_to_sign == 0 {
        return size;
    }

    // Add witness weight for inputs we still need to sign, plus the global
    // 2-byte marker+flag overhead only if the transaction does not already
    // contain any witness data.
    let overhead = if has_existing_witness || inputs_to_sign == 0 {
        0
    } else {
        WITNESS_OVERHEAD_BYTES
    };

    // If the transaction already has witness, each empty input already contributes
    // 1 byte (the `0x00` stack item count) to the serialized size. In that case,
    // we should add only the delta to reach the full witness size for those inputs.
    let per_input_added_bytes = if has_existing_witness {
        WITNESS_WEIGHT_BYTES.saturating_sub(1)
    } else {
        WITNESS_WEIGHT_BYTES
    };

    size + inputs_to_sign * per_input_added_bytes + overhead
}

pub(crate) fn estimate_final_tx_vsize(transaction: &Transaction) -> Result<usize, BitcoinTxError> {
    let weight = transaction.weight();
    let (inputs_to_sign, has_existing_witness) = inputs_to_sign_and_has_witness(transaction);

    if inputs_to_sign == 0 {
        return Ok(weight.to_vbytes_ceil() as usize);
    }

    // Add witness weight for inputs we still need to sign, plus the global
    // 2-byte marker+flag overhead only if the transaction does not already
    // contain any witness data.
    let overhead = if has_existing_witness || inputs_to_sign == 0 {
        0
    } else {
        WITNESS_OVERHEAD_WU
    };

    // Witness bytes contribute 1 WU per byte. The 2-byte marker+flag overhead
    // is part of the witness serialization and should be counted exactly once
    // when the transaction first gains witness. If the tx already has witness,
    // do not add it again here.
    // Also, in a segwit transaction, inputs with empty witness already account for
    // 1WU (the `0x00` stack item count) each, so add only the delta to reach the
    // full witness size for those inputs.
    let per_input_added_wu = if has_existing_witness {
        WITNESS_WEIGHT_BYTES.saturating_sub(1)
    } else {
        WITNESS_WEIGHT_BYTES
    };

    let extra_weight = Weight::from_wu_usize(inputs_to_sign * per_input_added_wu + overhead);

    let total_weight = weight
        .checked_add(extra_weight)
        .ok_or(BitcoinTxError::CalcOverflow)?;

    Ok(total_weight.to_vbytes_ceil() as usize)
}

pub(crate) fn calculate_fees_for_transaction(
    _remaining_btc: u64,
    transaction: &mut Transaction,
    total_size_of_pending_utxos: usize,
    fee_rate: &FeeRate,
) -> Result<(u64, u64), BitcoinTxError> {
    let base_tx_size = estimate_final_tx_vsize(transaction)?;
    let total_size = safe_add(base_tx_size, total_size_of_pending_utxos)?;

    msg!("base_tx_size: {:?}", base_tx_size);
    msg!("total_size: {:?}", total_size);

    let base_fee = fee_rate.fee(base_tx_size);
    let total_fee = fee_rate.fee(total_size);

    Ok((total_fee.to_sat(), base_fee.to_sat()))
}

pub(crate) fn adjust_transaction_to_pay_fees(
    transaction: &mut Transaction,
    tx_statuses: &MempoolInfo,
    total_btc_amount: u64,
    address_to_send_remaining_btc: Option<ScriptBuf>,
    fee_rate: &FeeRate,
) -> Result<(), BitcoinTxError> {
    let total_btc_used = transaction
        .output
        .iter()
        .map(|output| output.value.to_sat())
        .sum::<u64>();

    let (total_size_of_pending_utxos, total_fee_paid_of_pending_utxos) =
        (tx_statuses.total_size as usize, tx_statuses.total_fee);

    msg!("total_btc_amount: {:?}", total_btc_amount);
    msg!("total_btc_used: {:?}", total_btc_used);
    msg!(
        "total_fee_paid_of_pending_utxos: {:?}",
        total_fee_paid_of_pending_utxos
    );
    msg!(
        "total_size_of_pending_utxos: {:?}",
        total_size_of_pending_utxos
    );

    // Calculate remaining BTC after outputs
    let remaining_btc = safe_sub(total_btc_amount, total_btc_used)
        .map_err(|_| BitcoinTxError::NotEnoughAmountToCoverFees)?;

    // Get change without ancestors
    let (total_fee_with_ancestors, total_fee_without_ancestors) = calculate_fees_for_transaction(
        remaining_btc,
        transaction,
        total_size_of_pending_utxos,
        fee_rate,
    )?;

    msg!("total_fee_with_ancestors: {:?}", total_fee_with_ancestors);
    msg!(
        "total_fee_without_ancestors: {:?}",
        total_fee_without_ancestors
    );

    // Get available change with and without ancestors
    let available_for_change_without_ancestors =
        safe_sub(remaining_btc, total_fee_without_ancestors)
            .map_err(|_| BitcoinTxError::NotEnoughAmountToCoverFees)?;

    let available_for_change_with_ancestors = safe_sub(
        safe_add(remaining_btc, total_fee_paid_of_pending_utxos)?,
        total_fee_with_ancestors,
    )
    .map_err(|_| BitcoinTxError::NotEnoughAmountToCoverFees)?;

    // Get the minimum. We want to cover both the ancestors fees and ours.
    // But we don't want to use ancestors fees to pay ours.
    let available_for_change = min(
        available_for_change_without_ancestors,
        available_for_change_with_ancestors,
    );

    // Only add change output if we have enough to cover dust limit
    if let Some(change_script) = address_to_send_remaining_btc {
        if available_for_change >= DUST_LIMIT {
            // Add change output
            let txout = TxOut {
                value: Amount::from_sat(available_for_change),
                script_pubkey: change_script,
            };

            transaction.output.push(txout);

            // Recalculate fees with change output
            let (_, new_total_fee_without_ancestors) = calculate_fees_for_transaction(
                remaining_btc,
                transaction,
                total_size_of_pending_utxos,
                fee_rate,
            )?;

            let fee_difference =
                safe_sub(new_total_fee_without_ancestors, total_fee_without_ancestors)?;

            match safe_sub(available_for_change, fee_difference) {
                Ok(new_remaining_btc) if new_remaining_btc >= DUST_LIMIT => {
                    // Update change output with final amount
                    transaction.output.last_mut().unwrap().value =
                        Amount::from_sat(new_remaining_btc);
                }
                _ => {
                    // If we can't afford the change output or it would be dust, simply remove it
                    transaction.output.pop();
                }
            }
        }
    }

    Ok(())
}

pub fn estimate_tx_size_with_additional_inputs_outputs<C: PushPopCollection<InputToSign>>(
    transaction: &mut Transaction,
    inputs_to_sign: &C,
    new_potential_inputs_and_outputs: &NewPotentialInputsAndOutputs,
) -> Result<usize, BitcoinTxError> {
    add_reserved_inputs_and_outputs(
        transaction,
        inputs_to_sign,
        new_potential_inputs_and_outputs,
    )
    .map_err(|_| BitcoinTxError::InputToSignListFull)?;

    let total_size = estimate_final_tx_total_size(transaction);

    rollback_potential_inputs_and_outputs(transaction, new_potential_inputs_and_outputs);

    Ok(total_size)
}

pub fn estimate_tx_vsize_with_additional_inputs_outputs<C: PushPopCollection<InputToSign>>(
    transaction: &mut Transaction,
    inputs_to_sign: &mut C,
    new_potential_inputs_and_outputs: &NewPotentialInputsAndOutputs,
) -> Result<usize, BitcoinTxError> {
    add_reserved_inputs_and_outputs(
        transaction,
        inputs_to_sign,
        new_potential_inputs_and_outputs,
    )
    .map_err(|_| BitcoinTxError::InputToSignListFull)?;

    let total_vsize = estimate_final_tx_vsize(transaction)?;

    rollback_potential_inputs_and_outputs(transaction, new_potential_inputs_and_outputs);

    Ok(total_vsize)
}

fn add_reserved_inputs_and_outputs<C: PushPopCollection<InputToSign>>(
    transaction: &mut Transaction,
    inputs_to_sign: &C,
    new_potential_inputs_and_outputs: &NewPotentialInputsAndOutputs,
) -> Result<(), PushPopError> {
    if let Some(NewPotentialInputAmount {
        count,
        ref item,
        signer,
    }) = new_potential_inputs_and_outputs.inputs
    {
        // Pre-allocate capacity to avoid repeated reallocations
        transaction.input.reserve(count);

        let mut inputs_to_sign_len = inputs_to_sign.len();
        for _ in 0..count {
            if signer {
                if inputs_to_sign_len + 1 > inputs_to_sign.max_size() {
                    return Err(PushPopError::Full);
                }

                inputs_to_sign_len += 1;
            }

            transaction.input.push(item.clone());
        }
    }

    for NewPotentialOutputAmount { count, item } in new_potential_inputs_and_outputs.outputs.iter()
    {
        for _ in 0..*count {
            transaction.output.push(item.clone());
        }
    }

    Ok(())
}

fn rollback_potential_inputs_and_outputs(
    transaction: &mut Transaction,
    new_potential_inputs_and_outputs: &NewPotentialInputsAndOutputs,
) {
    if let Some(NewPotentialInputAmount {
        count,
        item: _,
        signer: _,
    }) = new_potential_inputs_and_outputs.inputs
    {
        let new_input_len = transaction.input.len() - count;
        transaction.input.truncate(new_input_len);
    }

    for NewPotentialOutputAmount { count, item: _ } in
        new_potential_inputs_and_outputs.outputs.iter()
    {
        let new_output_len = transaction.output.len() - *count;
        transaction.output.truncate(new_output_len);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        input_calc::{CONTROL_BLOCK_SIZE, REDEEM_SCRIPT_SIZE},
        NewPotentialInputAmount, NewPotentialOutputAmount,
    };

    use super::*;
    use arch_program::pubkey::Pubkey;
    use bitcoin::{
        absolute::LockTime, consensus::Decodable, key::constants::SCHNORR_SIGNATURE_SIZE,
        transaction::Version, Address, Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxIn,
        TxOut, Witness,
    };
    use satellite_collections::generic::push_pop::PushPopError;
    use std::str::FromStr;

    enum AddressType {
        Program,
        Account,
        User,
    }

    // Helper functions for creating test data
    fn create_mock_transaction() -> Transaction {
        Transaction {
            version: bitcoin::transaction::Version::TWO,
            lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
            input: vec![],
            output: vec![],
        }
    }

    fn create_mock_tx_in(outpoint: OutPoint) -> TxIn {
        TxIn {
            previous_output: outpoint,
            script_sig: ScriptBuf::new(),
            sequence: Sequence::MAX,
            witness: Witness::new(),
        }
    }

    fn create_mock_tx_out(value: u64) -> TxOut {
        TxOut {
            value: Amount::from_sat(value),
            script_pubkey: ScriptBuf::new(),
        }
    }

    fn create_mock_outpoint(txid: [u8; 32], vout: u32) -> OutPoint {
        OutPoint {
            txid: bitcoin::Txid::from_str(&hex::encode(txid)).unwrap(),
            vout,
        }
    }

    fn add_fake_witness_to_transaction(
        transaction: &mut Transaction,
        inputs_to_sign: &[InputToSign],
    ) {
        inputs_to_sign.iter().for_each(|input| {
            // Construct the witness with stack-allocated arrays
            let signature = [0u8; SCHNORR_SIGNATURE_SIZE];
            let redeem_script = [0u8; REDEEM_SCRIPT_SIZE];
            let control_block = [0u8; CONTROL_BLOCK_SIZE];

            let witness_items: [&[u8]; 3] = [&signature, &redeem_script, &control_block];

            transaction.input[input.index as usize].witness = Witness::from_slice(&witness_items);
        });
    }

    fn create_mock_address(address_type: AddressType) -> Address {
        match address_type {
            AddressType::Program => Address::from_str(
                &String::from_str("bcrt1qhwz8mxa0e5l7wep79rk765swffkmqvxzdmz5lt").unwrap(),
            )
            .unwrap()
            .require_network(bitcoin::Network::Regtest)
            .unwrap(),
            AddressType::Account => Address::from_str(
                &String::from_str(
                    "bcrt1ptccryszg6u3xvppg3scnh9xac5ke7qypvtsxqzgzut9j92k3h5tqfdxs47",
                )
                .unwrap(),
            )
            .unwrap()
            .require_network(bitcoin::Network::Regtest)
            .unwrap(),
            AddressType::User => Address::from_str(
                &String::from_str(
                    "bcrt1pkv5vcfxj4lj3anfnj7s8758ysw5kw54ukk0jdvs80gw6yg2c4v3s24lt2u",
                )
                .unwrap(),
            )
            .unwrap()
            .require_network(bitcoin::Network::Regtest)
            .unwrap(),
        }
    }

    #[derive(Debug, Default)]
    struct MockPushPopCollection {
        items: Vec<InputToSign>,
    }

    impl PushPopCollection<InputToSign> for MockPushPopCollection {
        fn push(&mut self, item: InputToSign) -> Result<(), PushPopError> {
            self.items.push(item);
            Ok(())
        }

        fn pop(&mut self) -> Option<InputToSign> {
            self.items.pop()
        }

        fn as_slice(&self) -> &[InputToSign] {
            &self.items
        }

        fn len(&self) -> usize {
            self.items.len()
        }

        fn max_size(&self) -> usize {
            usize::MAX
        }
    }

    #[test]
    fn test_add_reserved_inputs_and_outputs() {
        let mut transaction = create_mock_transaction();
        let mut inputs_to_sign = MockPushPopCollection::default();

        let potential_input = create_mock_tx_in(create_mock_outpoint([1; 32], 0));
        let potential_output = create_mock_tx_out(500);

        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 2,
                item: potential_input,
                signer: true,
            }),
            outputs: vec![NewPotentialOutputAmount {
                count: 3,
                item: potential_output,
            }],
        };

        add_reserved_inputs_and_outputs(
            &mut transaction,
            &mut inputs_to_sign,
            &new_potential_inputs_and_outputs,
        )
        .unwrap();

        assert_eq!(transaction.input.len(), 2);
        assert_eq!(transaction.output.len(), 3);
        // All newly added inputs should have empty witnesses and thus be considered to sign
        assert!(transaction.input.iter().all(|i| i.witness.is_empty()));
    }

    #[test]
    fn test_add_reserved_inputs_and_outputs_no_signer() {
        let mut transaction = create_mock_transaction();
        let mut inputs_to_sign = MockPushPopCollection::default();

        let potential_input = create_mock_tx_in(create_mock_outpoint([1; 32], 0));

        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 2,
                item: potential_input,
                signer: false,
            }),
            outputs: vec![],
        };

        add_reserved_inputs_and_outputs(
            &mut transaction,
            &mut inputs_to_sign,
            &new_potential_inputs_and_outputs,
        )
        .unwrap();

        assert_eq!(transaction.input.len(), 2);
        assert_eq!(inputs_to_sign.items.len(), 0); // No signers should be added
    }

    #[test]
    fn test_rollback_potential_inputs_and_outputs() {
        let mut transaction = create_mock_transaction();

        // Add some initial inputs and outputs
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([1; 32], 0)));
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([2; 32], 0)));
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([3; 32], 0)));

        transaction.output.push(create_mock_tx_out(1000));
        transaction.output.push(create_mock_tx_out(2000));
        transaction.output.push(create_mock_tx_out(3000));
        transaction.output.push(create_mock_tx_out(4000));

        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 2, // Remove last 2 inputs
                item: create_mock_tx_in(create_mock_outpoint([0; 32], 0)),
                signer: false,
            }),
            outputs: vec![NewPotentialOutputAmount {
                count: 3, // Remove last 3 outputs
                item: create_mock_tx_out(0),
            }],
        };

        rollback_potential_inputs_and_outputs(&mut transaction, &new_potential_inputs_and_outputs);

        assert_eq!(transaction.input.len(), 1);
        assert_eq!(transaction.output.len(), 1);
        assert_eq!(transaction.output[0].value.to_sat(), 1000);
    }

    #[test]
    fn test_rollback_with_no_potential_inputs() {
        let mut transaction = create_mock_transaction();
        transaction.output.push(create_mock_tx_out(1000));
        transaction.output.push(create_mock_tx_out(2000));

        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: None, // No potential inputs
            outputs: vec![NewPotentialOutputAmount {
                count: 1, // Remove 1 output
                item: create_mock_tx_out(0),
            }],
        };

        rollback_potential_inputs_and_outputs(&mut transaction, &new_potential_inputs_and_outputs);

        // Only outputs should be affected
        assert_eq!(transaction.input.len(), 0);
        assert_eq!(transaction.output.len(), 1);
        assert_eq!(transaction.output[0].value.to_sat(), 1000);
    }

    #[test]
    fn test_rollback_with_no_potential_outputs() {
        let mut transaction = create_mock_transaction();
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([1; 32], 0)));
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([2; 32], 0)));

        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 1, // Remove 1 input
                item: create_mock_tx_in(create_mock_outpoint([0; 32], 0)),
                signer: false,
            }),
            outputs: vec![], // No potential outputs
        };

        rollback_potential_inputs_and_outputs(&mut transaction, &new_potential_inputs_and_outputs);

        // Only inputs should be affected
        assert_eq!(transaction.input.len(), 1);
        assert_eq!(transaction.output.len(), 0);
    }

    #[test]
    fn test_add_reserved_inputs_with_existing_inputs() {
        let mut transaction = create_mock_transaction();
        let mut inputs_to_sign = MockPushPopCollection::default();
        let signer = Pubkey::default();

        // Add some existing inputs first
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([1; 32], 0)));
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([2; 32], 0)));
        inputs_to_sign
            .push(InputToSign { index: 0, signer })
            .unwrap();
        inputs_to_sign
            .push(InputToSign { index: 1, signer })
            .unwrap();

        let potential_input = create_mock_tx_in(create_mock_outpoint([3; 32], 0));
        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 3,
                item: potential_input,
                signer: true,
            }),
            outputs: vec![],
        };

        add_reserved_inputs_and_outputs(
            &mut transaction,
            &mut inputs_to_sign,
            &new_potential_inputs_and_outputs,
        )
        .unwrap();

        // Should have 2 existing + 3 new = 5 total inputs
        assert_eq!(transaction.input.len(), 5);
        // All inputs should still have empty witnesses and thus be considered to sign
        assert!(transaction.input.iter().all(|i| i.witness.is_empty()));
    }

    #[test]
    fn test_rollback_with_signers() {
        let mut transaction = create_mock_transaction();
        let mut inputs_to_sign = MockPushPopCollection::default();
        let signer = Pubkey::default();

        // Set up transaction with some inputs and corresponding signers
        for i in 0..5 {
            transaction
                .input
                .push(create_mock_tx_in(create_mock_outpoint([i as u8; 32], 0)));
            inputs_to_sign
                .push(InputToSign {
                    index: i as u32,
                    signer,
                })
                .unwrap();
        }

        // Add some outputs
        for i in 0..4 {
            transaction.output.push(create_mock_tx_out(1000 * (i + 1)));
        }

        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 2, // Remove last 2 inputs
                item: create_mock_tx_in(create_mock_outpoint([0; 32], 0)),
                signer: true, // With signer - should also rollback inputs_to_sign
            }),
            outputs: vec![NewPotentialOutputAmount {
                count: 3, // Remove last 3 outputs
                item: create_mock_tx_out(0),
            }],
        };

        rollback_potential_inputs_and_outputs(&mut transaction, &new_potential_inputs_and_outputs);

        // Should have 3 inputs and 1 output left
        assert_eq!(transaction.input.len(), 3);
        assert_eq!(transaction.output.len(), 1);
    }

    #[test]
    fn test_add_reserved_with_zero_count() {
        let mut transaction = create_mock_transaction();
        let mut inputs_to_sign = MockPushPopCollection::default();

        let potential_input = create_mock_tx_in(create_mock_outpoint([1; 32], 0));
        let potential_output = create_mock_tx_out(500);

        let new_potential_inputs_and_outputs = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 0, // Zero count
                item: potential_input,
                signer: true,
            }),
            outputs: vec![NewPotentialOutputAmount {
                count: 0, // Zero count
                item: potential_output,
            }],
        };

        add_reserved_inputs_and_outputs(
            &mut transaction,
            &mut inputs_to_sign,
            &new_potential_inputs_and_outputs,
        )
        .unwrap();

        // Nothing should be added
        assert_eq!(transaction.input.len(), 0);
        assert_eq!(transaction.output.len(), 0);
        assert_eq!(inputs_to_sign.items.len(), 0);
    }

    #[test]
    fn test_estimate_final_tx_total_and_vsize() {
        use crate::input_calc::{WITNESS_OVERHEAD_BYTES, WITNESS_WEIGHT_BYTES};

        let mut transaction = create_mock_transaction();
        transaction
            .input
            .push(create_mock_tx_in(create_mock_outpoint([1; 32], 0)));

        // --- Total size ---
        let expected_total_size =
            transaction.total_size() + WITNESS_WEIGHT_BYTES + WITNESS_OVERHEAD_BYTES;
        let calculated_total_size = super::estimate_final_tx_total_size(&transaction);
        assert_eq!(calculated_total_size, expected_total_size);

        // --- Virtual size ---
        let expected_vsize =
            transaction.vsize() + (WITNESS_WEIGHT_BYTES + WITNESS_OVERHEAD_BYTES) / 4;
        let calculated_vsize = super::estimate_final_tx_vsize(&transaction).unwrap();
        assert_eq!(calculated_vsize, expected_vsize);
    }

    #[test]
    fn test_calculate_fees_for_transaction() {
        let mut transaction = create_mock_transaction();
        // Add a dummy output so the transaction isn't empty
        transaction.output.push(create_mock_tx_out(10_000));

        let fee_rate = FeeRate::try_from(2.0).unwrap(); // 2 sats/vB

        // Assume the user still has 100k sats available to cover fees/change
        let (total_fee, base_fee) = super::calculate_fees_for_transaction(
            100_000,
            &mut transaction,
            0, // No ancestor transactions
            &fee_rate,
        )
        .expect("fee calculation should succeed");

        // Manual calculation for comparison
        let expected_base_fee = fee_rate
            .fee(super::estimate_final_tx_vsize(&transaction).unwrap())
            .to_sat();
        assert_eq!(base_fee, expected_base_fee);
        assert_eq!(total_fee, expected_base_fee); // No pending UTXOs so totals match
    }

    #[test]
    fn test_adjust_transaction_to_pay_fees_adds_change_output() {
        use crate::constants::DUST_LIMIT;

        // Build a transaction where 50_000 sats are already assigned to outputs
        let mut transaction = create_mock_transaction();
        transaction.output.push(create_mock_tx_out(50_000));

        let tx_statuses = MempoolInfo {
            total_fee: 0,
            total_size: 0,
        };

        // Provide 100_000 sats in total – 50_000 already used, 50_000 remain
        let total_btc_amount = 100_000u64;
        let fee_rate = FeeRate::try_from(1.0).unwrap(); // 1 sat/vB (very small to guarantee change output)

        let change_script = ScriptBuf::new();
        super::adjust_transaction_to_pay_fees(
            &mut transaction,
            &tx_statuses,
            total_btc_amount,
            Some(change_script.clone()),
            &fee_rate,
        )
        .expect("adjust_transaction_to_pay_fees should succeed");

        // We expect a second output containing the change (non-dust)
        assert_eq!(transaction.output.len(), 2);
        let change_output = &transaction.output[1];
        assert!(change_output.value.to_sat() >= DUST_LIMIT);
        assert_eq!(change_output.script_pubkey, change_script);
    }

    #[test]
    fn test_estimate_size_with_additional_inputs_outputs() {
        let mut transaction = create_mock_transaction();
        let mut inputs_to_sign = MockPushPopCollection::default();

        let potential_input = create_mock_tx_in(create_mock_outpoint([1; 32], 0));
        let potential_output = create_mock_tx_out(1_000);

        let new_potential = NewPotentialInputsAndOutputs {
            inputs: Some(NewPotentialInputAmount {
                count: 2,
                item: potential_input,
                signer: true,
            }),
            outputs: vec![NewPotentialOutputAmount {
                count: 1,
                item: potential_output,
            }],
        };

        // Capture baseline sizes (should be minimal since tx is empty)
        let base_total_size = super::estimate_final_tx_total_size(&transaction);
        let base_vsize = super::estimate_final_tx_vsize(&transaction).unwrap();

        // Calculate estimated sizes with the additional reserved IOs
        let est_total_size = super::estimate_tx_size_with_additional_inputs_outputs(
            &mut transaction,
            &mut inputs_to_sign,
            &new_potential,
        )
        .unwrap();

        let est_vsize = super::estimate_tx_vsize_with_additional_inputs_outputs(
            &mut transaction,
            &mut inputs_to_sign,
            &new_potential,
        )
        .unwrap();

        // The estimates must be strictly greater than the baseline
        assert!(est_total_size > base_total_size);
        assert!(est_vsize > base_vsize);

        // Ensure that the original transaction and inputs_to_sign remained untouched
        assert_eq!(transaction.input.len(), 0);
        assert_eq!(transaction.output.len(), 0);
        assert_eq!(inputs_to_sign.len(), 0);
    }

    #[test]
    fn test_adjust_transaction_to_pay_fees_success() {
        let mut transaction = create_mock_transaction();
        transaction.output.push(TxOut {
            value: Amount::from_sat(1000),
            script_pubkey: ScriptBuf::new(),
        });

        let total_btc_amount = 2000;
        let address_to_send_remaining_btc =
            Some(create_mock_address(AddressType::User).script_pubkey());
        let fee_rate = FeeRate::try_from(1.0).unwrap();
        let tx_statuses = MempoolInfo::default();

        let result = adjust_transaction_to_pay_fees(
            &mut transaction,
            &tx_statuses,
            total_btc_amount,
            address_to_send_remaining_btc,
            &fee_rate,
        );

        assert!(result.is_ok());
        assert_eq!(transaction.output.len(), 2);
        assert!(transaction.output[1].value.to_sat() < 1000);
    }

    #[test]
    fn test_adjust_transaction_to_pay_fees_not_enough_btc() {
        let mut transaction = create_mock_transaction();
        transaction.output.push(TxOut {
            value: Amount::from_sat(2000),
            script_pubkey: ScriptBuf::new(),
        });

        let total_btc_amount = 2000;
        let address_to_send_remaining_btc =
            Some(create_mock_address(AddressType::User).script_pubkey());
        let fee_rate = FeeRate::try_from(1.0).unwrap();
        let tx_statuses = MempoolInfo::default();

        let result = adjust_transaction_to_pay_fees(
            &mut transaction,
            &tx_statuses,
            total_btc_amount,
            address_to_send_remaining_btc,
            &fee_rate,
        );

        assert_eq!(result, Err(BitcoinTxError::NotEnoughAmountToCoverFees));
    }

    #[test]
    fn test_adjust_transaction_to_pay_fees_no_remaining_address() {
        let mut transaction = create_mock_transaction();
        transaction.output.push(TxOut {
            value: Amount::from_sat(1000),
            script_pubkey: ScriptBuf::new(),
        });

        let total_btc_amount = 2000;
        let address_to_send_remaining_btc: Option<ScriptBuf> = None;
        let fee_rate = FeeRate::try_from(1.0).unwrap();
        let tx_statuses = MempoolInfo::default();

        let result = adjust_transaction_to_pay_fees(
            &mut transaction,
            &tx_statuses,
            total_btc_amount,
            address_to_send_remaining_btc,
            &fee_rate,
        );

        assert!(result.is_ok());
        // No address provided; no change output should be added
        assert_eq!(transaction.output.len(), 1);
    }

    #[test]
    fn test_adjust_transaction_to_pay_fees_below_dust_limit() {
        let mut transaction = create_mock_transaction();
        transaction.output.push(TxOut {
            value: Amount::from_sat(1990),
            script_pubkey: ScriptBuf::new(),
        });

        let total_btc_amount = 2500;
        let address_to_send_remaining_btc =
            Some(create_mock_address(AddressType::User).script_pubkey());
        let fee_rate = FeeRate::try_from(1.0).unwrap();
        let tx_statuses = MempoolInfo::default();

        let result = adjust_transaction_to_pay_fees(
            &mut transaction,
            &tx_statuses,
            total_btc_amount,
            address_to_send_remaining_btc,
            &fee_rate,
        );

        assert!(result.is_ok());
        // Below dust: no change output should be added
        assert_eq!(transaction.output.len(), 1);
        assert!(result.is_ok());
        // Below dust: no change output should be added
        assert_eq!(transaction.output.len(), 1);
    }

    #[test]
    fn test_adjust_transaction_to_pay_fees_high_fee_rate() {
        let mut transaction = create_mock_transaction();
        transaction.output.push(TxOut {
            value: Amount::from_sat(1000),
            script_pubkey: ScriptBuf::new(),
        });

        let total_btc_amount = 12000;
        let address_to_send_remaining_btc =
            Some(create_mock_address(AddressType::User).script_pubkey());
        let fee_rate = FeeRate::try_from(100.0).unwrap();
        let tx_statuses = MempoolInfo::default();

        let result = adjust_transaction_to_pay_fees(
            &mut transaction,
            &tx_statuses,
            total_btc_amount,
            address_to_send_remaining_btc,
            &fee_rate,
        );

        assert!(result.is_ok());
        // With high fee rate and a change address, change output should be added
        assert_eq!(transaction.output.len(), 2);
    }

    #[test]
    fn test_compare_transaction_size_with_real_tx() {
        let tx_hex = "02000000000105758116853713a5a70c82887b926adda03fa3095f2485216a8ffd3359d91ab31a0000000000ffffffff50a694057e1c7272159e204638a7644fc53e0e5321aa3a3ce56b20a0ddfe0eb10200000000ffffffff4675c26f254ce76e27fb60d617043120653f502ff96b4f21db8a9251e2dfa05f0100000000ffffffff50a694057e1c7272159e204638a7644fc53e0e5321aa3a3ce56b20a0ddfe0eb10300000000ffffffff50a694057e1c7272159e204638a7644fc53e0e5321aa3a3ce56b20a0ddfe0eb10600000000ffffffff072202000000000000225120bb05c7618b8257e59869b6fcf1b5484d8721bf6d8e43e7c67afbfd15075f385022020000000000002251206d21bc4b6559a7395efe949e2fd3c71dff00eadfdbab811830522588eaced398dd030000000000002251202cc10bf07ec3fd89acbaffa5f4e00556d9641ca432380b5aa4378ab77662ec3922020000000000002251207747be095848f616170cde9025459529081bee916042118bb288768c855478a80000000000000000056a5d02160372ac3900000000002251207747be095848f616170cde9025459529081bee916042118bb288768c855478a84c020000000000002251202cc10bf07ec3fd89acbaffa5f4e00556d9641ca432380b5aa4378ab77662ec390340d71decbd1b576758e297af9acad32c228e2fabedf5740ee49f8abb2fe42c6bd18884f96f19e1147a92d7f42a4f456cd37582a68e7cc1b043a67e92c8fcc4ba384520d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c82ac6320b50628702cfb4d3ae4a0b0c1e3db05adaedadb95917014be86fabcdf9f0e23776821c0d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c8203405880944ff79614949d5c97bc725926c80d2e52b23b11f800bfd6493bb91bedc7cb77251dca334f59dabeab7059f63435887fa6ec9fce583762b4f509b68a7b984520d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c82ac63208b83375647a7cbfc61bf914b5a03b7f4ad05e9a08617793db9be3826d8ac01a66821c0d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c820141f476e0dba417df8bd57074976f319724c6a4d0fb92f626307fddbbcde116dfff4e741c96ea50786692405694dec49be46bd41313f40d124539f62fecd7076425830340d2d8b4a32ada603c4c6c2f9971455167efb42dc979880d14479ba7b473bc9e2f219813e478723a29463e5162a2a8f45a6555b18240960e36ea262b3b91da72824520d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c82ac6320f459378df0b7fee33978573c17811f581e78b2048cef120752d80673ffbfe2cd6821c0d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c820340f441354317de2d77a8788e59ffdd00f418d418fb9fc7b65f0fe2b10f988b9f6847c8e23dc7efbf3dbeaa172f77fe10cd6f910e7e135d1429caf6a49f2e5672834520d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c82ac6320f459378df0b7fee33978573c17811f581e78b2048cef120752d80673ffbfe2cd6821c0d8140907748c7f7c586fd1584be80bf039427162f8a5d2c4439fffae470b7c8200000000";
        let tx_raw = hex::decode(tx_hex).unwrap();
        let mut tx = Transaction::consensus_decode(&mut tx_raw.as_slice()).unwrap();

        // remove the last output
        tx.output.pop();

        // return the size of the witness of the first input
        println!("witness size: {:#?}", tx.input[0].witness.size());

        let original_vsize = tx.vsize();
        println!("tx: {:#?}", tx.vsize());
        println!("tx: {:#?}", tx.weight());

        // Remove the witness of all inputs except the third one.
        let mut total_weight_bytes_removed = 0;
        for i in 0..tx.input.len() {
            if i != 2 {
                total_weight_bytes_removed += tx.input[i].witness.size();
                tx.input[i].witness = Witness::new();
            }
        }

        println!(
            "total_weight_bytes_removed: {:#?}",
            total_weight_bytes_removed
        );

        let estimated_total_vsize = estimate_final_tx_vsize(&tx).unwrap();
        println!("estimated_total_vsize: {:#?}", estimated_total_vsize);

        assert_eq!(
            estimated_total_vsize, original_vsize,
            "estimated_total_vsize: {:#?} != original_vsize: {:#?}",
            estimated_total_vsize, original_vsize
        );
    }

    use proptest::prelude::*;

    #[test]
    fn display_witness_weights() {
        use bitcoin::{Transaction, TxIn, TxOut, Witness};

        for inputs in 1..100 {
            // Construct a transaction with 1 input and 1 output
            let mut tx = Transaction {
                version: Version(2),
                lock_time: LockTime::ZERO,
                input: vec![
                    TxIn {
                        previous_output: Default::default(),
                        script_sig: ScriptBuf::new(),
                        sequence: Sequence(0xFFFF_FFFF),
                        witness: Witness::new(), // empty for now
                    };
                    inputs
                ],
                output: vec![TxOut {
                    value: Amount::from_sat(1000),
                    script_pubkey: ScriptBuf::from_hex("6a").unwrap(), // OP_RETURN dummy
                }],
            };

            let inputs_to_sign = (0..inputs)
                .map(|i| InputToSign {
                    index: i as u32,
                    signer: Pubkey([0; 32]),
                })
                .collect::<Vec<_>>();

            let _estimated_total_size = estimate_final_tx_total_size(&tx);
            let estimated_total_vsize = estimate_final_tx_vsize(&tx).unwrap();

            // Now apply actual fake witness to validate correctness
            add_fake_witness_to_transaction(&mut tx, &inputs_to_sign);

            let _final_total_size = tx.total_size();
            let final_total_vsize = tx.vsize();

            println!(
                "Inputs: {} - Real size: {} - Estimated: {}, Diff: {}",
                inputs,
                final_total_vsize,
                estimated_total_vsize,
                (final_total_vsize as isize - estimated_total_vsize as isize)
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 99, ..ProptestConfig::default()
        })]
        #[test]
        fn test_witness_weight_constant(inputs in 1..100_usize) {
            use bitcoin::{Transaction, TxIn, TxOut, Witness};

             // Construct a transaction with 1 input and 1 output
            let mut tx = Transaction {
                version: Version(2),
                lock_time: LockTime::ZERO,
                input: vec![
                    TxIn {
                        previous_output: Default::default(),
                        script_sig: ScriptBuf::new(),
                        sequence: Sequence(0xFFFF_FFFF),
                        witness: Witness::new(), // empty for now
                    };
                    inputs
                ],
                output: vec![TxOut {
                    value: Amount::from_sat(1000),
                    script_pubkey: ScriptBuf::from_hex("6a").unwrap(), // OP_RETURN dummy
                }],
            };

            let inputs_to_sign = (0..inputs)
                .map(|i| InputToSign {
                    index: i as u32,
                    signer: Pubkey([0; 32]),
                })
                .collect::<Vec<_>>();

            let estimated_total_size = estimate_final_tx_total_size(&tx);
            let estimated_total_vsize = estimate_final_tx_vsize(&tx).unwrap() as isize;

            // Now apply actual fake witness to validate correctness
            add_fake_witness_to_transaction(&mut tx, &inputs_to_sign);

            let final_total_size = tx.total_size();
            let final_total_vsize = tx.vsize() as isize;

            assert_eq!(final_total_size, estimated_total_size);

            // Sometimes it's one byte more, sometimes it's one byte less because of rounding
            assert!((final_total_vsize - estimated_total_vsize) <= 1);
        }
    }
}
