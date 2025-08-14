use satellite_lang::prelude::*;

// Intentionally different program id than the one defined in Anchor.toml.
declare_id!("da075cb2ff5ec6817613de530b692a8735477769da47430cbd8154335c4a8327");

#[program]
mod declare_id {
    use super::*;

    pub fn initialize(_ctx: Context<Initialize>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize {
}
