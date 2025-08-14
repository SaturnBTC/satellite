use satellite_lang::prelude::*;

declare_id!("da075cb2ff5ec6817613de530b692a8735477769da47430cbd8154335c4a8327");

#[program]
pub mod ignore_non_accounts {
    use super::*;
    pub fn initialize(ctx: Context<Initialize>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    /// CHECK:
    checked1: UncheckedAccount<'info>,
    /// CHECK:
    checked2: AccountInfo<'info>,
}

#[derive(Debug)]
pub struct ShouldIgnore1<'info> {
    unchecked1: UncheckedAccount<'info>,
    unchecked2: AccountInfo<'info>,
}

pub struct ShouldIgnore2<'info> {
    unchecked1: UncheckedAccount<'info>,
    unchecked2: AccountInfo<'info>,
}
