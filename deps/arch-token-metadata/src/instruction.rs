//! Instruction types

use {
    arch_program::{program_error::ProgramError, pubkey::Pubkey},
    borsh::{BorshDeserialize, BorshSerialize},
};

/// Instructions supported by the token metadata program.
#[derive(BorshSerialize, BorshDeserialize, Debug, Clone, PartialEq)]
pub enum MetadataInstruction {
    /// Create core metadata for a token
    CreateMetadata {
        /// The name of the token
        name: String,
        /// The symbol of the token
        symbol: String,
        /// The image URI for the token
        image: String,
        /// The description of the token
        description: String,
        /// If true, metadata is immutable (no updates allowed)
        immutable: bool,
    },
    /// Update core metadata
    UpdateMetadata {
        /// Optional new name for the token
        name: Option<String>,
        /// Optional new symbol for the token
        symbol: Option<String>,
        /// Optional new image URI for the token
        image: Option<String>,
        /// Optional new description for the token
        description: Option<String>,
    },
    /// Create metadata attributes
    CreateAttributes {
        /// Key-value pairs for extensible attributes
        data: Vec<(String, String)>,
    },
    /// Replace metadata attributes
    ReplaceAttributes {
        /// Key-value pairs for extensible attributes
        data: Vec<(String, String)>,
    },
    /// Transfer update authority (must provide a new authority)
    TransferAuthority {
        /// New authority to transfer to
        new_authority: Pubkey,
    },
    /// Make metadata immutable (revoke update authority)
    MakeImmutable,
}

impl MetadataInstruction {
    /// Unpack a byte array into a MetadataInstruction
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        borsh::from_slice(input).map_err(|_| ProgramError::InvalidInstructionData)
    }

    /// Pack the MetadataInstruction into a byte array
    pub fn pack(&self) -> Vec<u8> {
        borsh::to_vec(self).unwrap()
    }
}
