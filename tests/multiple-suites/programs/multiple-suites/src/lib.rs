use satellite_lang::prelude::*;

declare_id!("da075cb2ff5ec6817613de530b692a8735477769da47430cbd8154335c4a8327");

#[program]
pub mod multiple_suites {
    use super::*;

    // _val to ensure tx are different so they don't get rejected.
    pub fn initialize(_ctx: Context<Initialize>, _val: u64) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize {}
