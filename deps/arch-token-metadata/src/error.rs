//! Error types

use {
    arch_program::{
        decode_error::DecodeError,
        msg,
        program_error::{PrintProgramError, ProgramError},
    },
    num_derive::FromPrimitive,
    thiserror::Error,
};

/// Errors that may be returned by the Token Metadata program.
#[derive(Clone, Debug, Eq, Error, FromPrimitive, PartialEq)]
pub enum MetadataError {
    // 0
    /// Invalid mint
    #[error("Invalid mint")]
    InvalidMint,
    /// Metadata already exists
    #[error("Metadata already exists")]
    MetadataAlreadyExists,
    /// Metadata not found
    #[error("Metadata not found")]
    MetadataNotFound,
    /// Invalid authority
    #[error("Invalid authority")]
    InvalidAuthority,
    /// Invalid instruction data
    #[error("Invalid instruction data")]
    InvalidInstructionData,
    /// String too long
    #[error("String too long")]
    StringTooLong,
    /// Too many attributes
    #[error("Too many attributes")]
    TooManyAttributes,
}

impl From<MetadataError> for ProgramError {
    fn from(e: MetadataError) -> Self {
        ProgramError::Custom(e as u32)
    }
}

impl<T> DecodeError<T> for MetadataError {
    fn type_of() -> &'static str {
        "MetadataError"
    }
}

impl PrintProgramError for MetadataError {
    fn print<E>(&self)
    where
        E: 'static
            + std::error::Error
            + DecodeError<E>
            + PrintProgramError
            + num_traits::FromPrimitive,
    {
        match self {
            MetadataError::InvalidMint => msg!("Error: Invalid mint"),
            MetadataError::MetadataAlreadyExists => msg!("Error: Metadata already exists"),
            MetadataError::MetadataNotFound => msg!("Error: Metadata not found"),
            MetadataError::InvalidAuthority => msg!("Error: Invalid authority"),
            MetadataError::InvalidInstructionData => msg!("Error: Invalid instruction data"),
            MetadataError::StringTooLong => msg!("Error: String too long"),
            MetadataError::TooManyAttributes => msg!("Error: Too many attributes"),
        }
    }
}
