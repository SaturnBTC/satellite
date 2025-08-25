//! State types and serialization sizes

use {
    arch_program::{
        program_error::ProgramError,
        program_pack::{IsInitialized, Pack, Sealed},
        pubkey::Pubkey,
    },
    borsh::{BorshDeserialize, BorshSerialize},
};

/// Maximum length for name
pub const NAME_MAX_LEN: usize = 256;

/// Maximum length for symbol
pub const SYMBOL_MAX_LEN: usize = 16;

/// Maximum length for image
pub const IMAGE_MAX_LEN: usize = 512;

/// Maximum length for description
pub const DESCRIPTION_MAX_LEN: usize = 512;

/// Maximum length for attribute key
pub const MAX_KEY_LENGTH: usize = 64;

/// Maximum length for attribute value
pub const MAX_VALUE_LENGTH: usize = 240;

/// Maximum number of attributes
pub const MAX_ATTRIBUTES: usize = 32;

/// Calculate the maximum serialized length (in bytes) for the TokenMetadata account using Borsh
/// String layout: 4-byte LE length prefix + bytes
/// Option<Pubkey> worst-case: 1-byte tag + 32 bytes
pub const TOKEN_METADATA_MAX_LEN: usize = 1 + // is_initialized (bool)
    32 + // mint
    (4 + NAME_MAX_LEN) +
    (4 + SYMBOL_MAX_LEN) +
    (4 + IMAGE_MAX_LEN) +
    (4 + DESCRIPTION_MAX_LEN) +
    (1 + 32); // update_authority = Some(Pubkey)

/// Calculate the maximum serialized length (in bytes) for the TokenMetadataAttributes account
/// Vec layout: 4-byte LE length + elements; each element is a tuple of two Strings
/// Tuple(String, String) layout: (4+key_len) + (4+value_len)
pub const TOKEN_METADATA_ATTRIBUTES_MAX_LEN: usize = 1 + // is_initialized (bool)
    32 + // mint
    4 + // vec length prefix
    (MAX_ATTRIBUTES * ((4 + MAX_KEY_LENGTH) + (4 + MAX_VALUE_LENGTH)));

/// Core metadata account - always present, optimized for performance
#[derive(BorshSerialize, BorshDeserialize, Debug, Clone, PartialEq)]
pub struct TokenMetadata {
    /// Initialization flag
    pub is_initialized: bool,
    /// The mint address this metadata belongs to
    pub mint: Pubkey,
    /// The name of the token
    pub name: String,
    /// The symbol of the token
    pub symbol: String,
    /// The image URI for the token
    pub image: String,
    /// The description of the token
    pub description: String,
    /// Optional update authority for the metadata
    pub update_authority: Option<Pubkey>,
}

impl Sealed for TokenMetadata {}
impl IsInitialized for TokenMetadata {
    fn is_initialized(&self) -> bool {
        self.is_initialized
    }
}

impl Pack for TokenMetadata {
    const LEN: usize = TOKEN_METADATA_MAX_LEN;

    fn unpack_from_slice(src: &[u8]) -> Result<Self, ProgramError> {
        // Use streaming deserialization so trailing zero padding is ignored
        let mut slice_ref: &[u8] = src;
        BorshDeserialize::deserialize(&mut slice_ref).map_err(|_| ProgramError::InvalidAccountData)
    }

    fn pack_into_slice(&self, dst: &mut [u8]) {
        let data = borsh::to_vec(self).unwrap();
        // Copy serialized data into destination; assume destination has been sized to LEN
        dst[..data.len()].copy_from_slice(&data);
        // Zero the remainder for determinism
        if data.len() < dst.len() {
            for b in &mut dst[data.len()..] {
                *b = 0;
            }
        }
    }
}

/// Optional metadata attributes account - linked to core metadata
#[derive(BorshSerialize, BorshDeserialize, Debug, Clone, PartialEq)]
pub struct TokenMetadataAttributes {
    /// Initialization flag
    pub is_initialized: bool,
    /// The mint address this attributes belong to
    pub mint: Pubkey,
    /// Key-value pairs for extensible attributes
    pub data: Vec<(String, String)>, // Key-value pairs for extensibility
}

impl Sealed for TokenMetadataAttributes {}
impl IsInitialized for TokenMetadataAttributes {
    fn is_initialized(&self) -> bool {
        self.is_initialized
    }
}

impl Pack for TokenMetadataAttributes {
    const LEN: usize = TOKEN_METADATA_ATTRIBUTES_MAX_LEN;

    fn unpack_from_slice(src: &[u8]) -> Result<Self, ProgramError> {
        let mut slice_ref: &[u8] = src;
        BorshDeserialize::deserialize(&mut slice_ref).map_err(|_| ProgramError::InvalidAccountData)
    }

    fn pack_into_slice(&self, dst: &mut [u8]) {
        let data = borsh::to_vec(self).unwrap();
        dst[..data.len()].copy_from_slice(&data);
        if data.len() < dst.len() {
            for b in &mut dst[data.len()..] {
                *b = 0;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use arch_program::program_pack::Pack;

    fn pk(byte: u8) -> Pubkey {
        let bytes = [byte; 32];
        Pubkey::from_slice(&bytes)
    }

    #[test]
    fn token_metadata_pack_unpack_roundtrip() {
        let md = TokenMetadata {
            is_initialized: true,
            mint: pk(1),
            name: "Arch Pioneer Token".to_string(),
            symbol: "APT".to_string(),
            image: "https://arweave.net/abc123.png".to_string(),
            description: "The first token launched on Arch Network".to_string(),
            update_authority: Some(pk(2)),
        };

        let mut buf = vec![0u8; TokenMetadata::LEN];
        TokenMetadata::pack_into_slice(&md, &mut buf);

        // First byte reflects is_initialized (borsh bool -> u8)
        assert_eq!(buf[0], 1);

        let md2 = TokenMetadata::unpack_from_slice(&buf).expect("unpack md");
        assert_eq!(md, md2);
    }

    #[test]
    fn token_metadata_unpack_ignores_trailing_zeros() {
        let md = TokenMetadata {
            is_initialized: true,
            mint: pk(9),
            name: "Name".to_string(),
            symbol: "SYM".to_string(),
            image: "img".to_string(),
            description: "desc".to_string(),
            update_authority: None,
        };

        let mut packed = borsh::to_vec(&md).unwrap();
        // Append a bunch of trailing zeros beyond the serialized size
        packed.extend_from_slice(&vec![0u8; 512]);

        let unpacked = TokenMetadata::unpack_from_slice(&packed).expect("unpack md");
        assert_eq!(md, unpacked);
    }

    #[test]
    fn token_metadata_attributes_pack_unpack_roundtrip() {
        let attrs = TokenMetadataAttributes {
            is_initialized: true,
            mint: pk(3),
            data: vec![
                ("key1".to_string(), "value1".to_string()),
                ("k".to_string(), "v".to_string()),
            ],
        };

        let mut buf = vec![0u8; TokenMetadataAttributes::LEN];
        TokenMetadataAttributes::pack_into_slice(&attrs, &mut buf);
        assert_eq!(buf[0], 1);

        let attrs2 = TokenMetadataAttributes::unpack_from_slice(&buf).expect("unpack attrs");
        assert_eq!(attrs, attrs2);
    }

    #[test]
    fn token_metadata_attributes_unpack_ignores_trailing_zeros() {
        let attrs = TokenMetadataAttributes {
            is_initialized: true,
            mint: pk(7),
            data: vec![("alpha".into(), "beta".into())],
        };

        let mut packed = borsh::to_vec(&attrs).unwrap();
        packed.extend_from_slice(&vec![0u8; 256]);

        let unpacked = TokenMetadataAttributes::unpack_from_slice(&packed).expect("unpack attrs");
        assert_eq!(attrs, unpacked);
    }
}
