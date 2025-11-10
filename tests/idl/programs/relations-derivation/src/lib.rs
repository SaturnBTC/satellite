use satellite_lang::prelude::*;

declare_id!("064fc96e880e59d5b1177621bf58079a860a90b9d03bd010a5fd8eb3a5000000");

#[program]
pub mod relations_derivation {
    use super::*;

    pub fn init_base(ctx: Context<InitBase>) -> Result<()> {
        ctx.accounts.account.my_account = ctx.accounts.my_account.key();
        ctx.accounts.account.bump = ctx.bumps.account;
        Ok(())
    }

    pub fn test_relation(_ctx: Context<TestRelation>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct InitBase<'info> {
    /// CHECK: yeah I know
    #[account(mut)]
    my_account: Signer<'info>,
    #[account(
      init,
      payer = my_account,
      seeds = [b"seed"],
      space = 100,
      bump,
    )]
    account: Account<'info, MyAccount>,
    system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Nested<'info> {
    /// CHECK: yeah I know
    my_account: UncheckedAccount<'info>,
    #[account(
      has_one = my_account,
      seeds = [b"seed"],
      bump = account.bump
    )]
    account: Account<'info, MyAccount>,
}

#[derive(Accounts)]
pub struct TestRelation<'info> {
    /// CHECK: yeah I know
    my_account: UncheckedAccount<'info>,
    #[account(
      has_one = my_account,
      seeds = [b"seed"],
      bump = account.bump
    )]
    account: Account<'info, MyAccount>,
    nested: Nested<'info>,
}

#[account]
pub struct MyAccount {
    pub my_account: Pubkey,
    pub bump: u8,
}
