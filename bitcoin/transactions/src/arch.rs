use arch_program::{program::get_runes_from_output, program_error::ProgramError, rune::RuneAmount, utxo::UtxoMeta};
use satellite_collections::generic::fixed_set::FixedCapacitySet;

use crate::error::BitcoinTxError;

pub fn get_runes<RS>(utxo: &UtxoMeta) -> Result<RS, ProgramError>
where
    RS: FixedCapacitySet<Item = RuneAmount> + Default,
{
    let txid = utxo.txid_big_endian();

    let runes = get_runes_from_output(txid, utxo.vout()).ok_or(ProgramError::Custom(
        BitcoinTxError::RuneOutputNotFound.into(),
    ))?;

    let mut rune_set = RS::default();

    for rune in runes.iter() {
        let rune_amount = RuneAmount {
            amount: rune.amount,
            id: rune.id,
        };

        rune_set
            .insert(rune_amount)
            .map_err(|_| BitcoinTxError::MoreRunesInUtxoThanMax)?;
    }

    Ok(rune_set)
}
