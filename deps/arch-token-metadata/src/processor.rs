//! Program state processor

use {
    crate::{
        error::MetadataError,
        find_attributes_pda_with_program, find_metadata_pda_with_program,
        instruction::MetadataInstruction,
        state::{
            TokenMetadata, TokenMetadataAttributes, DESCRIPTION_MAX_LEN, IMAGE_MAX_LEN,
            MAX_ATTRIBUTES, MAX_KEY_LENGTH, MAX_VALUE_LENGTH, NAME_MAX_LEN, SYMBOL_MAX_LEN,
        },
        ATTRIBUTES_SEED, METADATA_SEED,
    },
    apl_token::{self, state::Mint},
    arch_program::{
        account::{next_account_info, AccountInfo, MIN_ACCOUNT_LAMPORTS},
        entrypoint::ProgramResult,
        msg,
        program::invoke_signed,
        program_error::ProgramError,
        program_option::COption,
        program_pack::{IsInitialized, Pack},
        pubkey::Pubkey,
        system_instruction::create_account,
    },
};

/// Program state handler.
pub struct Processor {}

impl Processor {
    /// Process a single instruction
    pub fn process(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        instruction_data: &[u8],
    ) -> ProgramResult {
        let instruction = MetadataInstruction::unpack(instruction_data)?;

        match instruction {
            MetadataInstruction::CreateMetadata {
                name,
                symbol,
                image,
                description,
                immutable,
            } => Self::process_create_metadata(
                program_id,
                accounts,
                name,
                symbol,
                image,
                description,
                immutable,
            ),
            MetadataInstruction::UpdateMetadata {
                name,
                symbol,
                image,
                description,
            } => Self::process_update_metadata(accounts, name, symbol, image, description),
            MetadataInstruction::CreateAttributes { data } => {
                Self::process_create_attributes(program_id, accounts, data)
            }
            MetadataInstruction::ReplaceAttributes { data } => {
                Self::process_replace_attributes(program_id, accounts, data)
            }

            MetadataInstruction::TransferAuthority { new_authority } => {
                Self::process_transfer_authority(accounts, new_authority)
            }

            MetadataInstruction::MakeImmutable => Self::process_make_immutable(accounts),
        }
    }

    fn process_create_metadata(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        name: String,
        symbol: String,
        image: String,
        description: String,
        immutable: bool,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let payer_info = next_account_info(account_info_iter)?; // [writable, signer]
        let system_program_info = next_account_info(account_info_iter)?; // []
        let mint_info = next_account_info(account_info_iter)?; // []
        let metadata_info = next_account_info(account_info_iter)?; // [writable]
        let mint_authority_info = next_account_info(account_info_iter)?; // [signer]

        // Token mint must be owned by the token program
        if mint_info.owner != &apl_token::id() {
            msg!(
                "Mint is not owned by the token program expected {:?}, got {:?}",
                apl_token::id(),
                mint_info.owner
            );
            return Err(ProgramError::IncorrectProgramId);
        }

        // Deserialize mint and enforce authority policy
        let mint = Mint::unpack(&mint_info.data.borrow()) //
            .map_err(|_| ProgramError::InvalidAccountData)?;

        if !mint.is_initialized() {
            msg!("Mint is not initialized");
            return Err(ProgramError::UninitializedAccount);
        }

        // Check signer against mint authority, with freeze authority fallback
        let matched_signer: Option<Pubkey> = match mint.mint_authority {
            COption::Some(mint_auth) => {
                if cmp_pubkeys(&mint_auth, mint_authority_info.key) {
                    Some(mint_auth)
                } else {
                    msg!("Mint authority does not match expected authority");
                    return Err(MetadataError::InvalidAuthority.into());
                }
            }
            COption::None => match mint.freeze_authority {
                COption::Some(freeze_auth) => {
                    if cmp_pubkeys(&freeze_auth, mint_authority_info.key) {
                        Some(freeze_auth)
                    } else {
                        msg!("Freeze authority does not match expected authority");
                        return Err(MetadataError::InvalidAuthority.into());
                    }
                }
                COption::None => {
                    msg!("Mint has no mint or freeze authority");
                    return Err(MetadataError::InvalidAuthority.into());
                }
            },
        };

        // Validate mint authority is signer
        if !mint_authority_info.is_signer {
            msg!("Mint authority is not a signer");
            return Err(MetadataError::InvalidAuthority.into());
        }

        // Validate the metadata PDA address
        let (expected_md_pda, md_bump) = find_metadata_pda_with_program(program_id, mint_info.key);
        if !cmp_pubkeys(&expected_md_pda, metadata_info.key) {
            msg!("Metadata PDA does not match expected PDA");
            return Err(ProgramError::InvalidSeeds);
        }

        // Validate field sizes
        if name.len() > NAME_MAX_LEN
            || symbol.len() > SYMBOL_MAX_LEN
            || image.len() > IMAGE_MAX_LEN
            || description.len() > DESCRIPTION_MAX_LEN
        {
            msg!(
                "Metadata field size is too long: name={}/{}, symbol={}/{}, image={}/{}, description={}/{}",
                name.len(),
                NAME_MAX_LEN,
                symbol.len(),
                SYMBOL_MAX_LEN,
                image.len(),
                IMAGE_MAX_LEN,
                description.len(),
                DESCRIPTION_MAX_LEN,
            );
            return Err(MetadataError::StringTooLong.into());
        }

        // If not owned by this program, create metadata PDA via CPI using PDA seeds
        if metadata_info.owner != program_id {
            // Require correct system program id
            if *system_program_info.key != Pubkey::system_program() {
                msg!("System program id does not match expected system program id");
                return Err(ProgramError::IncorrectProgramId);
            }

            if !payer_info.is_signer {
                msg!("Payer is not a signer");
                return Err(ProgramError::MissingRequiredSignature);
            }

            let space = TokenMetadata::LEN as u64;
            let lamports = MIN_ACCOUNT_LAMPORTS;

            invoke_signed(
                &create_account(
                    payer_info.key,
                    metadata_info.key,
                    lamports,
                    space,
                    program_id,
                ),
                &[
                    payer_info.clone(),
                    metadata_info.clone(),
                    system_program_info.clone(),
                ],
                &[&[
                    METADATA_SEED, //
                    mint_info.key.as_ref(),
                    &[md_bump],
                ]],
            )?;
        }

        // Ensure not already initialized (zero-initialized account will have first byte == 0)
        {
            let data_ref = metadata_info.data.borrow();
            if !data_ref.is_empty() && data_ref[0] != 0 {
                return Err(MetadataError::MetadataAlreadyExists.into());
            }
        }

        // Write metadata
        let metadata = TokenMetadata {
            is_initialized: true,
            mint: *mint_info.key,
            name,
            symbol,
            image,
            description,
            update_authority: if immutable { None } else { matched_signer },
        };

        metadata.pack_into_slice(&mut metadata_info.data.borrow_mut());

        Ok(())
    }

    fn process_update_metadata(
        accounts: &[AccountInfo],
        name: Option<String>,
        symbol: Option<String>,
        image: Option<String>,
        description: Option<String>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let metadata_info = next_account_info(account_info_iter)?; // [writable]
        let update_authority_info = next_account_info(account_info_iter)?; // [signer]

        if !update_authority_info.is_signer {
            msg!("Update authority is not a signer");
            return Err(ProgramError::MissingRequiredSignature);
        }

        // Load existing metadata
        let mut metadata = TokenMetadata::unpack(&metadata_info.data.borrow())
            .map_err(|_| ProgramError::InvalidAccountData)?;

        if !metadata.is_initialized() {
            msg!("Metadata not initialized");
            return Err(ProgramError::UninitializedAccount);
        }

        // Enforce update authority (immutable if None)
        match metadata.update_authority {
            Some(current_auth) => {
                if !cmp_pubkeys(&current_auth, update_authority_info.key) {
                    msg!("Update authority does not match");
                    return Err(MetadataError::InvalidAuthority.into());
                }
            }
            None => {
                msg!("Metadata is immutable");
                return Err(MetadataError::InvalidAuthority.into());
            }
        }

        // Validate and apply optional fields
        if let Some(ref n) = name {
            if n.len() > NAME_MAX_LEN {
                return Err(MetadataError::StringTooLong.into());
            }
        }
        if let Some(ref s) = symbol {
            if s.len() > SYMBOL_MAX_LEN {
                return Err(MetadataError::StringTooLong.into());
            }
        }
        if let Some(ref i) = image {
            if i.len() > IMAGE_MAX_LEN {
                return Err(MetadataError::StringTooLong.into());
            }
        }
        if let Some(ref d) = description {
            if d.len() > DESCRIPTION_MAX_LEN {
                return Err(MetadataError::StringTooLong.into());
            }
        }

        if let Some(n) = name {
            metadata.name = n;
        }
        if let Some(s) = symbol {
            metadata.symbol = s;
        }
        if let Some(i) = image {
            metadata.image = i;
        }
        if let Some(d) = description {
            metadata.description = d;
        }

        metadata.pack_into_slice(&mut metadata_info.data.borrow_mut());
        Ok(())
    }

    fn process_create_attributes(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        data: Vec<(String, String)>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let payer_info = next_account_info(account_info_iter)?; // [writable, signer]
        let system_program_info = next_account_info(account_info_iter)?; // []
        let mint_info = next_account_info(account_info_iter)?; // []
        let attributes_info = next_account_info(account_info_iter)?; // [writable]
        let update_authority_info = next_account_info(account_info_iter)?; // [signer]
        let metadata_info = next_account_info(account_info_iter)?; // [] (readonly)

        if !payer_info.is_signer || !update_authority_info.is_signer {
            return Err(ProgramError::MissingRequiredSignature);
        }

        // Validate attribute PDA address using this program_id
        let (expected_attrs_pda, attrs_bump) =
            find_attributes_pda_with_program(program_id, mint_info.key);
        if !cmp_pubkeys(&expected_attrs_pda, attributes_info.key) {
            msg!("Attributes PDA does not match expected PDA");
            return Err(ProgramError::InvalidSeeds);
        }

        // Ensure metadata exists and authority matches
        let metadata = TokenMetadata::unpack(&metadata_info.data.borrow())
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if !metadata.is_initialized() || !cmp_pubkeys(&metadata.mint, mint_info.key) {
            msg!("Metadata not initialized or mint mismatch");
            return Err(ProgramError::InvalidAccountData);
        }

        match metadata.update_authority {
            Some(current_auth) => {
                if !cmp_pubkeys(&current_auth, update_authority_info.key) {
                    msg!("Update authority does not match");
                    return Err(MetadataError::InvalidAuthority.into());
                }
            }
            None => {
                msg!("Metadata is immutable");
                return Err(MetadataError::InvalidAuthority.into());
            }
        }

        // Validate vector sizes and elements
        if data.len() > MAX_ATTRIBUTES {
            msg!("Too many attributes: {} > {}", data.len(), MAX_ATTRIBUTES);
            return Err(MetadataError::TooManyAttributes.into());
        }
        for (k, v) in &data {
            if k.is_empty() || v.is_empty() {
                msg!("Attribute key and value must be non-empty");
                return Err(MetadataError::InvalidInstructionData.into());
            }
            if k.len() > MAX_KEY_LENGTH || v.len() > MAX_VALUE_LENGTH {
                msg!(
                    "Attribute key or value is too long: key={}/{}, value={}/{}",
                    k.len(),
                    MAX_KEY_LENGTH,
                    v.len(),
                    MAX_VALUE_LENGTH,
                );
                return Err(MetadataError::StringTooLong.into());
            }
        }

        // Allocate full max size so future replacements never need reallocation
        let required_space: u64 = TokenMetadataAttributes::LEN as u64;

        if attributes_info.owner != program_id {
            if *system_program_info.key != Pubkey::system_program() {
                msg!("System program id does not match expected system program id");
                return Err(ProgramError::IncorrectProgramId);
            }
            if !payer_info.is_signer {
                msg!("Payer is not a signer");
                return Err(ProgramError::MissingRequiredSignature);
            }
            let lamports = MIN_ACCOUNT_LAMPORTS;

            invoke_signed(
                &create_account(
                    payer_info.key,
                    attributes_info.key,
                    lamports,
                    required_space,
                    program_id,
                ),
                &[
                    payer_info.clone(),
                    attributes_info.clone(),
                    system_program_info.clone(),
                ],
                &[&[
                    ATTRIBUTES_SEED, //
                    mint_info.key.as_ref(),
                    &[attrs_bump],
                ]],
            )?;
        } else {
            let curr_len = attributes_info.data.borrow().len() as u64;
            if curr_len != required_space {
                msg!(
                    "Attributes account size mismatch: curr={} required={}",
                    curr_len,
                    required_space
                );
                return Err(ProgramError::InvalidAccountData);
            }
        }

        // Ensure not already initialized
        {
            let data_ref = attributes_info.data.borrow();
            if !data_ref.is_empty() && data_ref[0] != 0 {
                return Err(MetadataError::MetadataAlreadyExists.into());
            }
        }

        let attrs = TokenMetadataAttributes {
            is_initialized: true,
            mint: *mint_info.key,
            data,
        };
        attrs.pack_into_slice(&mut attributes_info.data.borrow_mut());
        Ok(())
    }

    fn process_replace_attributes(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        data: Vec<(String, String)>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let attributes_info = next_account_info(account_info_iter)?; // [writable]
        let update_authority_info = next_account_info(account_info_iter)?; // [signer]
        let metadata_info = next_account_info(account_info_iter)?; // [] (readonly)

        if !update_authority_info.is_signer {
            return Err(ProgramError::MissingRequiredSignature);
        }

        // Validate metadata and authority
        let metadata = TokenMetadata::unpack(&metadata_info.data.borrow())
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if !metadata.is_initialized() {
            return Err(ProgramError::UninitializedAccount);
        }
        match metadata.update_authority {
            Some(current_auth) => {
                if !cmp_pubkeys(&current_auth, update_authority_info.key) {
                    return Err(MetadataError::InvalidAuthority.into());
                }
            }
            None => return Err(MetadataError::InvalidAuthority.into()),
        }

        // Validate PDA
        let (expected_attrs_pda, _bump) =
            find_attributes_pda_with_program(program_id, &metadata.mint);
        if !cmp_pubkeys(&expected_attrs_pda, attributes_info.key) {
            return Err(ProgramError::InvalidSeeds);
        }

        // Ensure attributes exist
        let mut attrs = TokenMetadataAttributes::unpack(&attributes_info.data.borrow())
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if !attrs.is_initialized() {
            return Err(ProgramError::UninitializedAccount);
        }

        // Validate sizes
        if data.len() > MAX_ATTRIBUTES {
            return Err(MetadataError::TooManyAttributes.into());
        }
        for (k, v) in &data {
            if k.is_empty() || v.is_empty() {
                return Err(MetadataError::InvalidInstructionData.into());
            }
            if k.len() > MAX_KEY_LENGTH || v.len() > MAX_VALUE_LENGTH {
                return Err(MetadataError::StringTooLong.into());
            }
        }

        // Replace vector
        attrs.data = data;
        attrs.pack_into_slice(&mut attributes_info.data.borrow_mut());
        Ok(())
    }

    fn process_transfer_authority(
        accounts: &[AccountInfo],
        new_authority: Pubkey,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let metadata_info = next_account_info(account_info_iter)?; // [writable]
        let current_authority_info = next_account_info(account_info_iter)?; // [signer]

        if !current_authority_info.is_signer {
            msg!("Current authority is not a signer");
            return Err(ProgramError::MissingRequiredSignature);
        }

        let mut metadata = TokenMetadata::unpack(&metadata_info.data.borrow())
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if !metadata.is_initialized() {
            msg!("Metadata not initialized");
            return Err(ProgramError::UninitializedAccount);
        }

        match metadata.update_authority {
            Some(current_auth) => {
                if !cmp_pubkeys(&current_auth, current_authority_info.key) {
                    msg!("Signer is not current update authority");
                    return Err(MetadataError::InvalidAuthority.into());
                }
            }
            None => {
                msg!("Metadata is immutable; cannot transfer authority");
                return Err(MetadataError::InvalidAuthority.into());
            }
        }

        metadata.update_authority = Some(new_authority);
        metadata.pack_into_slice(&mut metadata_info.data.borrow_mut());
        Ok(())
    }

    fn process_make_immutable(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let metadata_info = next_account_info(account_info_iter)?; // [writable]
        let current_authority_info = next_account_info(account_info_iter)?; // [signer]

        if !current_authority_info.is_signer {
            msg!("Current authority is not a signer");
            return Err(ProgramError::MissingRequiredSignature);
        }

        let mut metadata = TokenMetadata::unpack(&metadata_info.data.borrow())
            .map_err(|_| ProgramError::InvalidAccountData)?;
        if !metadata.is_initialized() {
            msg!("Metadata not initialized");
            return Err(ProgramError::UninitializedAccount);
        }

        match metadata.update_authority {
            Some(current_auth) => {
                if !cmp_pubkeys(&current_auth, current_authority_info.key) {
                    msg!("Signer is not current update authority");
                    return Err(MetadataError::InvalidAuthority.into());
                }
            }
            None => {
                msg!("Metadata already immutable");
                return Err(MetadataError::InvalidAuthority.into());
            }
        }

        metadata.update_authority = None;
        metadata.pack_into_slice(&mut metadata_info.data.borrow_mut());
        Ok(())
    }
}

/// Checks two pubkeys for equality using a cheap memcmp
fn cmp_pubkeys(a: &Pubkey, b: &Pubkey) -> bool {
    arch_program::program_memory::sol_memcmp(a.as_ref(), b.as_ref(), 32) == 0
}
