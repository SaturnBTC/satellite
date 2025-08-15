/// Rent Calculation
// pub const DEFAULT_LAMPORTS_PER_BYTE_YEAR: u64 = 1_000_000_000 / 100 * 365 / (1024 * 1024);

// TODO: Temp value as the rent is becoming greater than MIN_LAMPORTS_REQUIRED,
// fix that to a good value then comback to this
pub const DEFAULT_LAMPORTS_PER_BYTE_YEAR: u64 = 2;

/// Default amount of time (in years) the balance has to include rent for the
/// account to be rent exempt.
pub const DEFAULT_EXEMPTION_THRESHOLD: f64 = 2.0;

/// Account storage overhead for calculation of base rent.
///
/// This is the number of bytes required to store an account with no data. It is
/// added to an accounts data length when calculating [`Rent::minimum_balance`].
pub const ACCOUNT_STORAGE_OVERHEAD: u64 = 128;

/// Minimum balance due for rent-exemption of a given account data size.
pub fn minimum_rent(data_len: usize) -> u64 {
    let bytes = data_len as u64;
    (ACCOUNT_STORAGE_OVERHEAD + bytes) * DEFAULT_LAMPORTS_PER_BYTE_YEAR
}

pub fn is_exempt(lamports: u64, data_len: usize) -> bool {
    let minimum_balance = minimum_rent(data_len);
    lamports >= minimum_balance
}
