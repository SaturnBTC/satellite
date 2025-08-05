use satellite_lang::arch_program::pubkey::Pubkey;
use satellite_lang::Result;
use satellite_lang::{context::CpiContext, Accounts};

pub use spl_memo;
pub use spl_memo::ID;

pub fn build_memo<'info>(ctx: CpiContext<'_, '_, '_, 'info, BuildMemo>, memo: &[u8]) -> Result<()> {
    let ix = spl_memo::build_memo(
        memo,
        &ctx.remaining_accounts
            .iter()
            .map(|account| account.key)
            .collect::<Vec<_>>(),
    );
    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &ctx.remaining_accounts,
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

#[derive(Accounts)]
pub struct BuildMemo {}

#[derive(Clone)]
pub struct Memo;

impl satellite_lang::Id for Memo {
    fn id() -> Pubkey {
        ID
    }
}
