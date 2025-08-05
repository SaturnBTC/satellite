use arch_program::{
    account::{AccountInfo, MIN_ACCOUNT_LAMPORTS},
    entrypoint::ProgramResult,
    program::invoke_signed,
    pubkey::Pubkey,
    system_instruction,
};

/// Creates associated token account using Program Derived Address for the given
/// seeds
pub fn create_pda_account<'a>(
    payer: &AccountInfo<'a>,
    space: usize,
    owner: &Pubkey,
    system_program: &AccountInfo<'a>,
    new_pda_account: &AccountInfo<'a>,
    new_pda_signer_seeds: &[&[u8]],
) -> ProgramResult {
    invoke_signed(
        &system_instruction::create_account(
            payer.key,
            new_pda_account.key,
            MIN_ACCOUNT_LAMPORTS,
            space as u64,
            owner,
        ),
        &[
            payer.clone(),
            new_pda_account.clone(),
            system_program.clone(),
        ],
        &[new_pda_signer_seeds],
    )
}
