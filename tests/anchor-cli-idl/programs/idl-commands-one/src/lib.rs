use satellite_lang::prelude::*;

declare_id!("1c381d9cafb1ff3703d313f8f5c2a6b1683af97c6158120bfc3df0ae0ada05ca");

#[program]
pub mod idl_commands_one {
    use super::*;

    pub fn initialize(_ctx: Context<Initialize>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize {}
