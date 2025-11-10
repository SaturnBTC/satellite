use satellite_lang::arch_program::account::AccountInfo;
use satellite_lang::arch_program::pubkey::Pubkey;
use satellite_lang::Result;
use satellite_lang::{context::CpiContext, Accounts};

pub fn memo_transfer_initialize<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, MemoTransfer<'info>>,
) -> Result<()> {
    let ix = spl_token_2022::extension::memo_transfer::instruction::enable_required_transfer_memos(
        ctx.accounts.token_program_id.key,
        ctx.accounts.account.key,
        ctx.accounts.owner.key,
        &[],
    )?;
    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &[
            ctx.accounts.token_program_id,
            ctx.accounts.account,
            ctx.accounts.owner,
        ],
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

pub fn memo_transfer_disable<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, MemoTransfer<'info>>,
) -> Result<()> {
    let ix =
        spl_token_2022::extension::memo_transfer::instruction::disable_required_transfer_memos(
            ctx.accounts.token_program_id.key,
            ctx.accounts.account.key,
            ctx.accounts.owner.key,
            &[],
        )?;
    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &[
            ctx.accounts.token_program_id,
            ctx.accounts.account,
            ctx.accounts.owner,
        ],
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

#[derive(Accounts)]
pub struct MemoTransfer<'info> {
    pub token_program_id: AccountInfo<'info>,
    pub account: AccountInfo<'info>,
    pub owner: AccountInfo<'info>,
}
