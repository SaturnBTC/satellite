#![deny(missing_docs)]
#![cfg_attr(not(test), forbid(unsafe_code))]

//! Arch Network Token Metadata Standard

pub mod error;
pub mod instruction;
pub mod processor;
pub mod state;

// Exclude the on-chain entrypoint when building unit tests or when the
// consumer opts into the "no-entrypoint" feature (host-side contexts).
#[cfg(all(not(feature = "no-entrypoint"), not(test)))]
mod entrypoint;

use arch_program::{entrypoint::ProgramResult, program_error::ProgramError, pubkey::Pubkey};

/// The program ID for the Arch Token Metadata program
pub fn id() -> Pubkey {
    Pubkey::from_slice(b"arch-metadata000000000000000000")
}

/// Checks that the supplied program ID is the correct one for Arch Token Metadata
pub fn check_program_account(program_id: &Pubkey) -> ProgramResult {
    if program_id != &id() {
        return Err(ProgramError::IncorrectProgramId);
    }
    Ok(())
}

/// PDA seed for metadata account
pub const METADATA_SEED: &[u8] = b"metadata";

/// PDA seed for attributes account
pub const ATTRIBUTES_SEED: &[u8] = b"attributes";

/// Helper to derive the `TokenMetadata` PDA for a given mint
pub fn find_metadata_pda_with_program(program_id: &Pubkey, mint: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[METADATA_SEED, mint.as_ref()], program_id)
}

/// Helper to derive the `TokenMetadataAttributes` PDA for a given mint
pub fn find_attributes_pda_with_program(program_id: &Pubkey, mint: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[ATTRIBUTES_SEED, mint.as_ref()], program_id)
}
