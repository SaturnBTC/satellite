use satellite_lang::prelude::*;

declare_id!("0280a7b33cb9d0abc42a8df9d500280512746f9b507acef2e8eb222a69a00000");

#[program]
pub mod ambiguous_discriminator {
    use super::*;

    /// Compilation should error due to ambiguous discriminators.
    pub fn check_accounts(_ctx: Context<CheckAccounts>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct CheckAccounts<'info> {
    pub some_account: Account<'info, SomeAccount>,
    pub another_account: Account<'info, AnotherAccount>,
}

#[account(discriminator = 1)]
pub struct SomeAccount {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

#[account(discriminator = [1, 2, 3, 4])]
pub struct AnotherAccount {
    pub a: u32,
}
