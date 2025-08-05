use bitcode::{Decode, Encode};
use borsh::{BorshDeserialize, BorshSerialize};
#[cfg(feature = "fuzzing")]
use libfuzzer_sys::arbitrary;
use serde::{Deserialize, Serialize};
use std::fmt::Display;
use thiserror::Error;

#[derive(
    Default,
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize,
    BorshSerialize,
    BorshDeserialize,
    Encode,
    Decode,
)]
#[cfg_attr(feature = "fuzzing", derive(arbitrary::Arbitrary))]
pub struct Hash([u8; 32]);

impl AsRef<[u8; 32]> for Hash {
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

#[derive(Error, Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum HashError {
    #[error("Invalid hash length {0}")]
    InvalidLength(usize),

    #[error("Invalid hex string {0}")]
    InvalidHex(String),
}

impl From<hex::FromHexError> for HashError {
    fn from(err: hex::FromHexError) -> Self {
        HashError::InvalidHex(err.to_string())
    }
}

impl Display for Hash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", hex::encode(self.0))
    }
}

impl From<[u8; 32]> for Hash {
    fn from(value: [u8; 32]) -> Self {
        Hash(value)
    }
}

impl From<Hash> for String {
    fn from(hash: Hash) -> Self {
        hash.to_string()
    }
}

impl TryFrom<String> for Hash {
    type Error = HashError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Hash::from_str(&value)
    }
}

impl TryFrom<&str> for Hash {
    type Error = HashError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Hash::from_str(value)
    }
}

impl Hash {
    pub fn from_str(value: &str) -> Result<Self, HashError> {
        let hash = hex::decode(value)?;
        if hash.len() != 32 {
            return Err(HashError::InvalidLength(hash.len()));
        }
        Ok(Hash(hash.try_into().expect("just checked length")))
    }

    pub fn to_string(&self) -> String {
        hex::encode(self.0)
    }

    pub fn to_array(&self) -> [u8; 32] {
        self.0
    }

    pub fn to_string_short(&self) -> String {
        hex::encode(&self.0[..4])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_from_valid_string() {
        let string = "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef".to_string();
        let _hash = Hash::from_str(&string).unwrap();
    }

    #[test]
    fn test_hash_round_trip() {
        let string = "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef".to_string();
        let hash = Hash::from_str(&string).unwrap();
        assert_eq!(hash.to_string(), string);
    }

    #[test]
    fn test_hash_from_invalid_len_string() {
        let string = "1234567890abce".to_string();
        let result = Hash::from_str(&string);
        assert!(result.is_err());
        println!("Invalid length error : {:?}", result.err());
    }

    #[test]
    fn test_hash_from_invalid_hex_string() {
        let string = "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdex".to_string();
        let result = Hash::from_str(&string);
        assert!(result.is_err());
        println!("Invalid hex error : {:?}", result.err());
    }

    #[test]
    fn test_hash_to_array() {
        let string = "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef".to_string();
        let hash = Hash::from_str(&string).unwrap();
        let array = hash.to_array();
        assert_eq!(array, hash.0);
    }
}
