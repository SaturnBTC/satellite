//! This example demonstrates the ability to compose together multiple
//! structs deriving `Accounts`. See `CompositeUpdate`, below.

use satellite_lang::prelude::*;

declare_id!("c57bb0250886348a9353b75fd16f4867a4c23698857127ab712f6f22a6c8a8f1");

#[program]
mod composite {
    use super::*;
    pub fn initialize(_ctx: Context<Initialize>) -> Result<()> {
        Ok(())
    }

    pub fn composite_update(
        ctx: Context<CompositeUpdate>,
        dummy_a: u64,
        dummy_b: u64,
    ) -> Result<()> {
        let a = &mut ctx.accounts.foo.dummy_a;
        let b = &mut ctx.accounts.bar.dummy_b;

        a.data = dummy_a;
        b.data = dummy_b;

        Ok(())
    }
}

#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(zero)]
    pub dummy_a: Account<'info, DummyA>,
    #[account(zero)]
    pub dummy_b: Account<'info, DummyB>,
}

#[derive(Accounts)]
pub struct CompositeUpdate<'info> {
    foo: Foo<'info>,
    bar: Bar<'info>,
}

#[derive(Accounts)]
pub struct Foo<'info> {
    #[account(mut)]
    pub dummy_a: Account<'info, DummyA>,
}

#[derive(Accounts)]
pub struct Bar<'info> {
    #[account(mut)]
    pub dummy_b: Account<'info, DummyB>,
}

#[account]
pub struct DummyA {
    pub data: u64,
}

#[account]
pub struct DummyB {
    pub data: u64,
}
