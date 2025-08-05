use std::cell::Ref;

use crate::utxo_info::UtxoInfo;

/// A trait for types that can hold a list of BTC utxos.
///
/// This is used to hold the BTC utxos that are used to pay for the transaction.
/// It is used to avoid having to pass the list of utxos to every function that needs them.
pub trait BtcUtxoHolder {
    fn btc_utxos(&self) -> &[UtxoInfo];
}

impl<'a, T> BtcUtxoHolder for Ref<'a, T>
where
    T: BtcUtxoHolder + ?Sized,
{
    #[inline]
    fn btc_utxos(&self) -> &[UtxoInfo] {
        (**self).btc_utxos()
    }
}


impl BtcUtxoHolder for UtxoInfo {
    #[inline]
    fn btc_utxos(&self) -> &[UtxoInfo] {
        std::slice::from_ref(self)
    }
}
