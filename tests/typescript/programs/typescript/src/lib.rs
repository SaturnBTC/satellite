//! The typescript example serves to show how one would setup an Anchor
//! workspace with TypeScript tests and migrations.

use satellite_lang::prelude::*;

declare_id!("da075cb2ff5ec6817613de530b692a8735477769da47430cbd8154335c4a8327");

#[program]
pub mod typescript {
    use super::*;
    pub fn initialize(ctx: Context<Initialize>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize {}
