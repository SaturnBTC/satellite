use satellite_lang::arch_program::account::AccountInfo;
use satellite_lang::arch_program::pubkey::Pubkey;
use satellite_lang::Result;
use satellite_lang::{context::CpiContext, Accounts};

pub use apl_associated_token_account;
pub use apl_associated_token_account::get_associated_token_address_and_bump_seed;

pub fn create<'info>(ctx: CpiContext<'_, '_, '_, 'info, Create<'info>>) -> Result<()> {
    let ix = apl_associated_token_account::create_associated_token_account(
        ctx.accounts.payer.key,
        ctx.accounts.associated_token.key,
        ctx.accounts.authority.key,
        ctx.accounts.mint.key,
        ctx.accounts.token_program.key,
        ctx.accounts.system_program.key,
    );
    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &[
            ctx.accounts.payer,
            ctx.accounts.associated_token,
            ctx.accounts.authority,
            ctx.accounts.mint,
            ctx.accounts.system_program,
            ctx.accounts.token_program,
        ],
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

// pub fn create_idempotent<'info>(
//     ctx: CpiContext<'_, '_, '_, 'info, CreateIdempotent<'info>>,
// ) -> Result<()> {
//     let ix = apl_associated_token_account::instruction::create_associated_token_account_idempotent(
//         ctx.accounts.payer.key,
//         ctx.accounts.authority.key,
//         ctx.accounts.mint.key,
//         ctx.accounts.token_program.key,
//     );
//     satellite_lang::arch_program::program::invoke_signed(
//         &ix,
//         &[
//             ctx.accounts.payer,
//             ctx.accounts.associated_token,
//             ctx.accounts.authority,
//             ctx.accounts.mint,
//             ctx.accounts.system_program,
//             ctx.accounts.token_program,
//         ],
//         ctx.signer_seeds,
//     )
//     .map_err(Into::into)
// }

#[derive(Accounts)]
pub struct Create<'info> {
    pub payer: AccountInfo<'info>,
    pub associated_token: AccountInfo<'info>,
    pub authority: AccountInfo<'info>,
    pub mint: AccountInfo<'info>,
    pub system_program: AccountInfo<'info>,
    pub token_program: AccountInfo<'info>,
}

type CreateIdempotent<'info> = Create<'info>;

#[derive(Clone)]
pub struct AssociatedToken;

impl satellite_lang::Id for AssociatedToken {
    fn id() -> Pubkey {
        apl_associated_token_account::id()
    }
}
