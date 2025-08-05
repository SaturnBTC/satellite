use satellite_lang::arch_program::account::AccountInfo;
use satellite_lang::arch_program::pubkey::Pubkey;
use satellite_lang::Result;
use satellite_lang::{context::CpiContext, Accounts};

pub fn group_member_pointer_initialize<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, GroupMemberPointerInitialize<'info>>,
    authority: Option<Pubkey>,
    member_address: Option<Pubkey>,
) -> Result<()> {
    let ix = spl_token_2022::extension::group_member_pointer::instruction::initialize(
        ctx.accounts.token_program_id.key,
        ctx.accounts.mint.key,
        authority,
        member_address,
    )?;
    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &[ctx.accounts.token_program_id, ctx.accounts.mint],
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

#[derive(Accounts)]
pub struct GroupMemberPointerInitialize<'info> {
    pub token_program_id: AccountInfo<'info>,
    pub mint: AccountInfo<'info>,
}

pub fn group_member_pointer_update<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, GroupMemberPointerUpdate<'info>>,
    member_address: Option<Pubkey>,
) -> Result<()> {
    let ix = spl_token_2022::extension::group_member_pointer::instruction::update(
        ctx.accounts.token_program_id.key,
        ctx.accounts.mint.key,
        ctx.accounts.authority.key,
        &[],
        member_address,
    )?;
    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &[
            ctx.accounts.token_program_id,
            ctx.accounts.mint,
            ctx.accounts.authority,
        ],
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

#[derive(Accounts)]
pub struct GroupMemberPointerUpdate<'info> {
    pub token_program_id: AccountInfo<'info>,
    pub mint: AccountInfo<'info>,
    pub authority: AccountInfo<'info>,
}
