//! Build-only test exercising metadata account constraints.

use satellite_apl::metadata::{ArchTokenMetadataAccount, ArchTokenMetadataAttributesAccount};
use satellite_lang::prelude::*;

declare_id!("054a752fa3ef8be54b17ca4e6a0ca5595bf8a64d43b5df4cee58af7800000000");

#[program]
pub mod metadata {
    use super::*;

    pub fn check(_ctx: Context<Check>) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Check<'info> {
    pub mint: AccountInfo<'info>,
    pub update_authority: Signer<'info>,

    // Validate core metadata account belongs to `mint` and is governed by `update_authority`.
    #[account(
        metadata::mint = mint,
        metadata::update_authority = update_authority,
    )]
    pub metadata: Account<'info, ArchTokenMetadataAccount>,

    #[account(
        has_one = mint,
    )]
    pub attributes: Account<'info, ArchTokenMetadataAttributesAccount>,
}
