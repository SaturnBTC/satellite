use satellite_lang::prelude::*;

declare_id!("b5a4b93ff7a81b189c5395b8118ace6334000d2a6b777e23fb3486e7b25d071d");

#[program]
pub mod idl_commands_two {
    use super::*;

    pub fn uninitialize(_ctx: Context<Initialize>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize {}
