use arch_program::{account::AccountMeta, instruction::Instruction, pubkey::Pubkey};

pub fn create_associated_token_account(
    program_id: &Pubkey,
    payer: &Pubkey,
    associated_token: &Pubkey,
    authority: &Pubkey,
    mint: &Pubkey,
    system_program: &Pubkey,
    token_program: &Pubkey,
) -> Instruction {
    let accounts = vec![
        AccountMeta::new(*payer, true),
        AccountMeta::new(*associated_token, false),
        AccountMeta::new_readonly(*authority, false),
        AccountMeta::new_readonly(*mint, false),
        AccountMeta::new_readonly(*system_program, false),
        AccountMeta::new_readonly(*token_program, false),
    ];

    let instruction = Instruction::new_with_borsh(*program_id, &(), accounts);

    instruction
}
