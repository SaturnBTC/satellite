use satellite_lang::prelude::*;

declare_id!("cf794749d58bda6ab20f4533af68a74e07cfc691985bc4aa1e270c6000000000");

#[program]
pub mod external {
    use super::*;

    pub fn initialize(_ctx: Context<Initialize>) -> Result<()> {
        Ok(())
    }
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct MyStruct {
    some_field: u8,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub enum MyEnum {
    Unit,
    Named { name: String },
    Tuple(String),
}

pub struct NonBorshStruct {
    pub data: i32,
}

#[derive(Accounts)]
pub struct Initialize {}
