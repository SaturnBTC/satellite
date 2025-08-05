//! Program state processor

mod tools;

use arch_program::{
    account::{next_account_info, AccountInfo},
    entrypoint::ProgramResult,
    msg,
    program::invoke,
    program_error::ProgramError,
    program_pack::Pack,
    pubkey::Pubkey,
};
use tools::create_pda_account;

#[cfg(not(feature = "no-entrypoint"))]
use arch_program::entrypoint;

#[cfg(not(feature = "no-entrypoint"))]
entrypoint!(process_instruction);

/// Instruction processor
pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    _input: &[u8],
) -> ProgramResult {
    let account_info_iter = &mut accounts.iter();

    let funder_info = next_account_info(account_info_iter)?;
    let associated_token_account_info = next_account_info(account_info_iter)?;
    let wallet_account_info = next_account_info(account_info_iter)?;
    let spl_token_mint_info = next_account_info(account_info_iter)?;
    let system_program_info = next_account_info(account_info_iter)?;
    let spl_token_program_info = next_account_info(account_info_iter)?;
    let spl_token_program_id = spl_token_program_info.key;

    let (associated_token_address, bump_seed) = get_associated_token_address_and_bump_seed(
        wallet_account_info.key,
        spl_token_mint_info.key,
        program_id,
    );
    if associated_token_address != *associated_token_account_info.key {
        msg!("Error: Associated address does not match seed derivation");
        return Err(ProgramError::InvalidSeeds);
    }

    let associated_token_account_signer_seeds: &[&[_]] = &[
        &wallet_account_info.key.serialize(),
        &apl_token::id().serialize(),
        &spl_token_mint_info.key.serialize(),
        &[bump_seed],
    ];

    create_pda_account(
        funder_info,
        apl_token::state::Account::LEN,
        spl_token_program_info.key,
        system_program_info,
        associated_token_account_info,
        associated_token_account_signer_seeds,
    )?;
    msg!("Initialize the associated token account");
    invoke(
        &apl_token::instruction::initialize_account3(
            spl_token_program_id,
            associated_token_account_info.key,
            spl_token_mint_info.key,
            wallet_account_info.key,
        )?,
        &[
            associated_token_account_info.clone(),
            spl_token_mint_info.clone(),
            wallet_account_info.clone(),
            spl_token_program_info.clone(),
        ],
    )
}

pub fn id() -> Pubkey {
    Pubkey::from_slice(b"associated-token-account00000000")
}

pub fn get_associated_token_address_and_bump_seed(
    wallet_address: &Pubkey,
    spl_token_mint_address: &Pubkey,
    program_id: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            &wallet_address.serialize(),
            &apl_token::id().serialize(),
            &spl_token_mint_address.serialize(),
        ],
        program_id,
    )
}

pub mod instruction;
