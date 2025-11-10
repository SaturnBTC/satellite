//! Testing of handling of remaining accounts with anchor Account structs

use account::*;
use satellite_lang::prelude::*;
use satellite_apl::token::TokenAccount;
use context::*;

mod account;
mod context;

declare_id!("0650a501e94bd3b441cab863c435da3983521dd7ed2537dbd5875d3d50000000");

#[program]
pub mod remaining_accounts {
    use super::*;

    pub fn test_init(_ctx: Context<TestInit>) -> Result<()> {
        Ok(())
    }

    pub fn test_init_another(_ctx: Context<TestInitAnother>) -> Result<()> {
        Ok(())
    }

    pub fn test_remaining_accounts<'c: 'info, 'info>(
        ctx: Context<'_, '_, 'c, 'info, TestRemainingAccounts>,
    ) -> Result<()> {
        let remaining_accounts_iter = &mut ctx.remaining_accounts.iter();

        let token_account =
            Account::<TokenAccount>::try_from(next_account_info(remaining_accounts_iter)?)?;

        let data_account_info = next_account_info(remaining_accounts_iter)?;
        require_eq!(data_account_info.is_writable, true);
        let mut data = Account::<Data>::try_from(data_account_info)?;

        data.someone = token_account.owner;
        data.exit(ctx.program_id)?;

        Ok(())
    }
}
