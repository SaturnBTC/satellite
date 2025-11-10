use satellite_lang::arch_program::program_pack::{IsInitialized, Pack};
use satellite_lang::prelude::{
    AccountInfo, AccountMeta, Accounts, CpiContext, Pubkey, Result, ToAccountInfos,
};
use satellite_lang::system_program::SYSTEM_PROGRAM_ID;

pub use apl_token_metadata as arch_md;

/// Program ID for Arch Token Metadata
pub use arch_md::id as ID;

/// Create core metadata for a token
pub fn create_metadata<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, CreateMetadata<'info>>,
    name: String,
    symbol: String,
    image: String,
    description: String,
    immutable: bool,
) -> Result<()> {
    let ix_data = arch_md::instruction::MetadataInstruction::CreateMetadata {
        name,
        symbol,
        image,
        description,
        immutable,
    }
    .pack();

    let ix = satellite_lang::arch_program::instruction::Instruction {
        program_id: arch_md::id(),
        accounts: vec![
            AccountMeta::new(*ctx.accounts.payer.key, true),
            AccountMeta::new_readonly(SYSTEM_PROGRAM_ID, false),
            AccountMeta::new_readonly(*ctx.accounts.mint.key, false),
            AccountMeta::new(*ctx.accounts.metadata.key, false),
            AccountMeta::new_readonly(*ctx.accounts.mint_authority.key, true),
        ],
        data: ix_data,
    };

    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &ToAccountInfos::to_account_infos(&ctx),
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

/// Update core metadata
pub fn update_metadata<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, UpdateMetadata<'info>>,
    name: Option<String>,
    symbol: Option<String>,
    image: Option<String>,
    description: Option<String>,
) -> Result<()> {
    let ix_data = arch_md::instruction::MetadataInstruction::UpdateMetadata {
        name,
        symbol,
        image,
        description,
    }
    .pack();

    let ix = satellite_lang::arch_program::instruction::Instruction {
        program_id: arch_md::id(),
        accounts: vec![
            AccountMeta::new(*ctx.accounts.metadata.key, false),
            AccountMeta::new_readonly(*ctx.accounts.update_authority.key, true),
        ],
        data: ix_data,
    };

    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &ToAccountInfos::to_account_infos(&ctx),
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

/// Create attributes account
pub fn create_attributes<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, CreateAttributes<'info>>,
    data: Vec<(String, String)>,
) -> Result<()> {
    let ix_data = arch_md::instruction::MetadataInstruction::CreateAttributes { data }.pack();

    let ix = satellite_lang::arch_program::instruction::Instruction {
        program_id: arch_md::id(),
        accounts: vec![
            AccountMeta::new(*ctx.accounts.payer.key, true),
            AccountMeta::new_readonly(satellite_lang::system_program::SYSTEM_PROGRAM_ID, false),
            AccountMeta::new_readonly(*ctx.accounts.mint.key, false),
            AccountMeta::new(*ctx.accounts.attributes.key, false),
            AccountMeta::new_readonly(*ctx.accounts.update_authority.key, true),
            AccountMeta::new_readonly(*ctx.accounts.metadata.key, false),
        ],
        data: ix_data,
    };

    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &ToAccountInfos::to_account_infos(&ctx),
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

/// Replace attributes vector
pub fn replace_attributes<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, ReplaceAttributes<'info>>,
    data: Vec<(String, String)>,
) -> Result<()> {
    let ix_data = arch_md::instruction::MetadataInstruction::ReplaceAttributes { data }.pack();

    let ix = satellite_lang::arch_program::instruction::Instruction {
        program_id: arch_md::id(),
        accounts: vec![
            AccountMeta::new(*ctx.accounts.attributes.key, false),
            AccountMeta::new_readonly(*ctx.accounts.update_authority.key, true),
            AccountMeta::new_readonly(*ctx.accounts.metadata.key, false),
        ],
        data: ix_data,
    };

    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &ToAccountInfos::to_account_infos(&ctx),
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

/// Transfer update authority to a new authority
pub fn transfer_authority<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, TransferAuthority<'info>>,
    new_authority: Pubkey,
) -> Result<()> {
    let ix_data = arch_md::instruction::MetadataInstruction::TransferAuthority { new_authority };
    let ix = satellite_lang::arch_program::instruction::Instruction {
        program_id: arch_md::id(),
        accounts: vec![
            AccountMeta::new(*ctx.accounts.metadata.key, false),
            AccountMeta::new_readonly(*ctx.accounts.current_authority.key, true),
        ],
        data: ix_data.pack(),
    };

    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &ToAccountInfos::to_account_infos(&ctx),
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

/// Make metadata immutable (revoke update authority)
pub fn make_immutable<'info>(
    ctx: CpiContext<'_, '_, '_, 'info, MakeImmutable<'info>>,
) -> Result<()> {
    let ix_data = arch_md::instruction::MetadataInstruction::MakeImmutable.pack();
    let ix = satellite_lang::arch_program::instruction::Instruction {
        program_id: arch_md::id(),
        accounts: vec![
            AccountMeta::new(*ctx.accounts.metadata.key, false),
            AccountMeta::new_readonly(*ctx.accounts.current_authority.key, true),
        ],
        data: ix_data,
    };

    satellite_lang::arch_program::program::invoke_signed(
        &ix,
        &ToAccountInfos::to_account_infos(&ctx),
        ctx.signer_seeds,
    )
    .map_err(Into::into)
}

#[derive(Accounts)]
pub struct CreateMetadata<'info> {
    pub payer: AccountInfo<'info>,          // [writable, signer]
    pub system_program: AccountInfo<'info>, // []
    pub mint: AccountInfo<'info>,           // []
    pub metadata: AccountInfo<'info>,       // [writable]
    pub mint_authority: AccountInfo<'info>, // [signer]
}

#[derive(Accounts)]
pub struct UpdateMetadata<'info> {
    pub metadata: AccountInfo<'info>,         // [writable]
    pub update_authority: AccountInfo<'info>, // [signer]
}

#[derive(Accounts)]
pub struct CreateAttributes<'info> {
    pub payer: AccountInfo<'info>,            // [writable, signer]
    pub system_program: AccountInfo<'info>,   // []
    pub mint: AccountInfo<'info>,             // []
    pub attributes: AccountInfo<'info>,       // [writable]
    pub update_authority: AccountInfo<'info>, // [signer]
    pub metadata: AccountInfo<'info>,         // [] (readonly)
}

#[derive(Accounts)]
pub struct ReplaceAttributes<'info> {
    pub attributes: AccountInfo<'info>,       // [writable]
    pub update_authority: AccountInfo<'info>, // [signer]
    pub metadata: AccountInfo<'info>,         // [] (readonly)
}

#[derive(Accounts)]
pub struct TransferAuthority<'info> {
    pub metadata: AccountInfo<'info>,          // [writable]
    pub current_authority: AccountInfo<'info>, // [signer]
}

#[derive(Accounts)]
pub struct MakeImmutable<'info> {
    pub metadata: AccountInfo<'info>,          // [writable]
    pub current_authority: AccountInfo<'info>, // [signer]
}

#[derive(Clone)]
pub struct ArchMetadata;

impl satellite_lang::Id for ArchMetadata {
    fn id() -> Pubkey {
        arch_md::id()
    }
}

// --------------------------------------------------------------------------------
// Account wrappers for Arch Token Metadata state
// --------------------------------------------------------------------------------
use satellite_lang::error::ErrorCode;
use std::ops::Deref;

#[derive(Clone, Debug, PartialEq)]
pub struct ArchTokenMetadataAccount(arch_md::state::TokenMetadata);

impl satellite_lang::AccountDeserialize for ArchTokenMetadataAccount {
    fn try_deserialize(buf: &mut &[u8]) -> satellite_lang::Result<Self> {
        let md = Self::try_deserialize_unchecked(buf)?;
        if !md.0.is_initialized() {
            return Err(ErrorCode::AccountNotInitialized.into());
        }
        Ok(md)
    }

    fn try_deserialize_unchecked(buf: &mut &[u8]) -> satellite_lang::Result<Self> {
        let md = arch_md::state::TokenMetadata::unpack_from_slice(buf)
            .map_err(satellite_lang::error::Error::from)?;
        Ok(Self(md))
    }
}

impl satellite_lang::AccountSerialize for ArchTokenMetadataAccount {}

impl satellite_lang::Owner for ArchTokenMetadataAccount {
    fn owner() -> Pubkey {
        arch_md::id()
    }
}

impl Deref for ArchTokenMetadataAccount {
    type Target = arch_md::state::TokenMetadata;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArchTokenMetadataAttributesAccount(arch_md::state::TokenMetadataAttributes);

impl satellite_lang::AccountDeserialize for ArchTokenMetadataAttributesAccount {
    fn try_deserialize(buf: &mut &[u8]) -> satellite_lang::Result<Self> {
        let acc = Self::try_deserialize_unchecked(buf)?;
        if !acc.0.is_initialized() {
            return Err(ErrorCode::AccountNotInitialized.into());
        }
        Ok(acc)
    }

    fn try_deserialize_unchecked(buf: &mut &[u8]) -> satellite_lang::Result<Self> {
        let acc = arch_md::state::TokenMetadataAttributes::unpack_from_slice(buf)
            .map_err(satellite_lang::error::Error::from)?;
        Ok(Self(acc))
    }
}

impl satellite_lang::AccountSerialize for ArchTokenMetadataAttributesAccount {}

impl satellite_lang::Owner for ArchTokenMetadataAttributesAccount {
    fn owner() -> Pubkey {
        arch_md::id()
    }
}

impl Deref for ArchTokenMetadataAttributesAccount {
    type Target = arch_md::state::TokenMetadataAttributes;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
