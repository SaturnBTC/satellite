use borsh::io::{Error as IoError, ErrorKind as IoErrorKind};
use borsh::{BorshDeserialize, BorshSerialize};

/// Maximum script length accepted by the protocol.
pub const MAX_BTC_SCRIPT_BYTES: usize =
    satellite_bitcoin_transactions::constants::MAX_BTC_SCRIPT_BYTES;

/// Strongly-typed Bitcoin script pubkey with length validation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScriptPubkey(Vec<u8>);

impl ScriptPubkey {
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    #[inline]
    pub fn into_vec(self) -> Vec<u8> {
        self.0
    }
}

impl TryFrom<Vec<u8>> for ScriptPubkey {
    type Error = ScriptPubkeyError;
    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        if value.is_empty() || value.len() > MAX_BTC_SCRIPT_BYTES {
            return Err(ScriptPubkeyError::InvalidLength);
        }
        Ok(ScriptPubkey(value))
    }
}

impl BorshSerialize for ScriptPubkey {
    fn serialize<W: borsh::io::Write>(&self, writer: &mut W) -> std::result::Result<(), IoError> {
        borsh::BorshSerialize::serialize(&self.0, writer)
    }
}

impl BorshDeserialize for ScriptPubkey {
    fn deserialize_reader<R: borsh::io::Read>(
        reader: &mut R,
    ) -> std::result::Result<Self, IoError> {
        let value = Vec::<u8>::deserialize_reader(reader)?;
        if value.is_empty() || value.len() > MAX_BTC_SCRIPT_BYTES {
            return Err(IoError::new(
                IoErrorKind::InvalidData,
                "script_pubkey length invalid",
            ));
        }
        Ok(ScriptPubkey(value))
    }
}

impl From<ScriptPubkey> for bitcoin::ScriptBuf {
    fn from(value: ScriptPubkey) -> Self {
        bitcoin::ScriptBuf::from_bytes(value.0)
    }
}

impl Default for ScriptPubkey {
    fn default() -> Self {
        ScriptPubkey(Vec::new())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScriptPubkeyError {
    InvalidLength,
}

impl core::fmt::Display for ScriptPubkeyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ScriptPubkeyError::InvalidLength => write!(f, "invalid script_pubkey length"),
        }
    }
}
