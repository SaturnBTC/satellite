use crate::account::MIN_ACCOUNT_LAMPORTS;

pub struct Rent;

impl Rent {
    pub fn minimum_balance(_units: u64) -> u64 {
        MIN_ACCOUNT_LAMPORTS
    }

    pub fn is_exempt(lamports: u64, data_len: u64) -> bool {
        lamports >= MIN_ACCOUNT_LAMPORTS && data_len == 0
    }
}
