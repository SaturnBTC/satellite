//! Program state processor

use {
    crate::{
        amount_to_ui_amount_string_trimmed,
        error::TokenError,
        instruction::{is_valid_signer_index, AuthorityType, TokenInstruction, MAX_SIGNERS},
        state::{Account, AccountState, Mint, Multisig},
        try_ui_amount_into_amount,
    },
    arch_program::{
        account::{next_account_info, AccountInfo},
        entrypoint::ProgramResult,
        msg,
        program::set_return_data,
        program_error::ProgramError,
        program_memory::sol_memcmp,
        program_option::COption,
        program_pack::{IsInitialized, Pack},
        pubkey::{Pubkey, PUBKEY_BYTES},
        system_program::SYSTEM_PROGRAM_ID,
    },
};

/// Program state handler.
pub struct Processor {}
impl Processor {
    fn _process_initialize_mint(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;

        let mut mint = Mint::unpack_unchecked(&mint_info.data.borrow())?;
        if mint.is_initialized {
            return Err(TokenError::AlreadyInUse.into());
        }

        mint.mint_authority = COption::Some(mint_authority);
        mint.decimals = decimals;
        mint.is_initialized = true;
        mint.freeze_authority = freeze_authority;

        Mint::pack(mint, &mut mint_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes an [`InitializeMint`](enum.TokenInstruction.html) instruction.
    pub fn process_initialize_mint(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
    ) -> ProgramResult {
        Self::_process_initialize_mint(accounts, decimals, mint_authority, freeze_authority)
    }

    /// Processes an [`InitializeMint2`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_mint2(
        accounts: &[AccountInfo],
        decimals: u8,
        mint_authority: Pubkey,
        freeze_authority: COption<Pubkey>,
    ) -> ProgramResult {
        Self::_process_initialize_mint(accounts, decimals, mint_authority, freeze_authority)
    }

    fn _process_initialize_account(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        owner: Option<&Pubkey>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let new_account_info = next_account_info(account_info_iter)?;
        let mint_info = next_account_info(account_info_iter)?;
        let owner = if let Some(owner) = owner {
            owner
        } else {
            next_account_info(account_info_iter)?.key
        };

        let mut account = Account::unpack_unchecked(&new_account_info.data.borrow())?;
        if account.is_initialized() {
            return Err(TokenError::AlreadyInUse.into());
        }

        Self::check_account_owner(program_id, mint_info)?;
        let _ = Mint::unpack(&mint_info.data.borrow_mut())
            .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;

        account.mint = *mint_info.key;
        account.owner = *owner;
        account.close_authority = COption::None;
        account.delegate = COption::None;
        account.delegated_amount = 0;
        account.state = AccountState::Initialized;

        Account::pack(account, &mut new_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes an [`InitializeAccount`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_account(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
    ) -> ProgramResult {
        Self::_process_initialize_account(program_id, accounts, None)
    }

    /// Processes an [`InitializeAccount2`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_account2(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        owner: Pubkey,
    ) -> ProgramResult {
        Self::_process_initialize_account(program_id, accounts, Some(&owner))
    }

    /// Processes an [`InitializeAccount3`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_account3(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        owner: Pubkey,
    ) -> ProgramResult {
        Self::_process_initialize_account(program_id, accounts, Some(&owner))
    }

    fn _process_initialize_multisig(accounts: &[AccountInfo], m: u8) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let multisig_info = next_account_info(account_info_iter)?;

        let mut multisig = Multisig::unpack_unchecked(&multisig_info.data.borrow())?;
        if multisig.is_initialized {
            return Err(TokenError::AlreadyInUse.into());
        }

        let signer_infos = account_info_iter.as_slice();
        multisig.m = m;
        multisig.n = signer_infos.len() as u8;
        if !is_valid_signer_index(multisig.n as usize) {
            return Err(TokenError::InvalidNumberOfProvidedSigners.into());
        }
        if !is_valid_signer_index(multisig.m as usize) {
            return Err(TokenError::InvalidNumberOfRequiredSigners.into());
        }
        for (i, signer_info) in signer_infos.iter().enumerate() {
            multisig.signers[i] = *signer_info.key;
        }
        multisig.is_initialized = true;

        Multisig::pack(multisig, &mut multisig_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`InitializeMultisig`](enum.TokenInstruction.html)
    /// instruction.
    pub fn process_initialize_multisig(accounts: &[AccountInfo], m: u8) -> ProgramResult {
        Self::_process_initialize_multisig(accounts, m)
    }

    /// Processes a [`Transfer`](enum.TokenInstruction.html) instruction.
    pub fn process_transfer(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();

        let source_account_info = next_account_info(account_info_iter)?;

        let expected_mint_info = if let Some(expected_decimals) = expected_decimals {
            Some((next_account_info(account_info_iter)?, expected_decimals))
        } else {
            None
        };

        let destination_account_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;
        let mut destination_account = Account::unpack(&destination_account_info.data.borrow())?;

        if source_account.is_frozen() || destination_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }
        if source_account.amount < amount {
            return Err(TokenError::InsufficientFunds.into());
        }
        if !Self::cmp_pubkeys(&source_account.mint, &destination_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        if let Some((mint_info, expected_decimals)) = expected_mint_info {
            if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
                return Err(TokenError::MintMismatch.into());
            }

            let mint = Mint::unpack(&mint_info.data.borrow_mut())?;
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        let self_transfer =
            Self::cmp_pubkeys(source_account_info.key, destination_account_info.key);

        match source_account.delegate {
            COption::Some(ref delegate) if Self::cmp_pubkeys(authority_info.key, delegate) => {
                Self::validate_owner(
                    program_id,
                    delegate,
                    authority_info,
                    account_info_iter.as_slice(),
                )?;
                if source_account.delegated_amount < amount {
                    return Err(TokenError::InsufficientFunds.into());
                }
                if !self_transfer {
                    source_account.delegated_amount = source_account
                        .delegated_amount
                        .checked_sub(amount)
                        .ok_or(TokenError::Overflow)?;
                    if source_account.delegated_amount == 0 {
                        source_account.delegate = COption::None;
                    }
                }
            }
            _ => Self::validate_owner(
                program_id,
                &source_account.owner,
                authority_info,
                account_info_iter.as_slice(),
            )?,
        };

        if self_transfer || amount == 0 {
            Self::check_account_owner(program_id, source_account_info)?;
            Self::check_account_owner(program_id, destination_account_info)?;
        }

        // This check MUST occur just before the amounts are manipulated
        // to ensure self-transfers are fully validated
        if self_transfer {
            return Ok(());
        }

        source_account.amount = source_account
            .amount
            .checked_sub(amount)
            .ok_or(TokenError::Overflow)?;
        destination_account.amount = destination_account
            .amount
            .checked_add(amount)
            .ok_or(TokenError::Overflow)?;

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;
        Account::pack(
            destination_account,
            &mut destination_account_info.data.borrow_mut(),
        )?;

        Ok(())
    }

    /// Processes an [`Approve`](enum.TokenInstruction.html) instruction.
    pub fn process_approve(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();

        let source_account_info = next_account_info(account_info_iter)?;

        let expected_mint_info = if let Some(expected_decimals) = expected_decimals {
            Some((next_account_info(account_info_iter)?, expected_decimals))
        } else {
            None
        };
        let delegate_info = next_account_info(account_info_iter)?;
        let owner_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;

        if source_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }

        if let Some((mint_info, expected_decimals)) = expected_mint_info {
            if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
                return Err(TokenError::MintMismatch.into());
            }

            let mint = Mint::unpack(&mint_info.data.borrow_mut())?;
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        Self::validate_owner(
            program_id,
            &source_account.owner,
            owner_info,
            account_info_iter.as_slice(),
        )?;

        source_account.delegate = COption::Some(*delegate_info.key);
        source_account.delegated_amount = amount;

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes an [`Revoke`](enum.TokenInstruction.html) instruction.
    pub fn process_revoke(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let source_account_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;

        let owner_info = next_account_info(account_info_iter)?;

        if source_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }

        Self::validate_owner(
            program_id,
            &source_account.owner,
            owner_info,
            account_info_iter.as_slice(),
        )?;

        source_account.delegate = COption::None;
        source_account.delegated_amount = 0;

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`SetAuthority`](enum.TokenInstruction.html) instruction.
    pub fn process_set_authority(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        authority_type: AuthorityType,
        new_authority: COption<Pubkey>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let account_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        if account_info.data_len() == Account::get_packed_len() {
            let mut account = Account::unpack(&account_info.data.borrow())?;

            if account.is_frozen() {
                return Err(TokenError::AccountFrozen.into());
            }

            match authority_type {
                AuthorityType::AccountOwner => {
                    Self::validate_owner(
                        program_id,
                        &account.owner,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;

                    if let COption::Some(authority) = new_authority {
                        account.owner = authority;
                    } else {
                        return Err(TokenError::InvalidInstruction.into());
                    }

                    account.delegate = COption::None;
                    account.delegated_amount = 0;
                }
                AuthorityType::CloseAccount => {
                    let authority = account.close_authority.unwrap_or(account.owner);
                    Self::validate_owner(
                        program_id,
                        &authority,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;
                    account.close_authority = new_authority;
                }
                _ => {
                    return Err(TokenError::AuthorityTypeNotSupported.into());
                }
            }
            Account::pack(account, &mut account_info.data.borrow_mut())?;
        } else if account_info.data_len() == Mint::get_packed_len() {
            let mut mint = Mint::unpack(&account_info.data.borrow())?;
            match authority_type {
                AuthorityType::MintTokens => {
                    // Once a mint's supply is fixed, it cannot be undone by setting a new
                    // mint_authority
                    let mint_authority = mint
                        .mint_authority
                        .ok_or(Into::<ProgramError>::into(TokenError::FixedSupply))?;
                    Self::validate_owner(
                        program_id,
                        &mint_authority,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;
                    mint.mint_authority = new_authority;
                }
                AuthorityType::FreezeAccount => {
                    // Once a mint's freeze authority is disabled, it cannot be re-enabled by
                    // setting a new freeze_authority
                    let freeze_authority = mint
                        .freeze_authority
                        .ok_or(Into::<ProgramError>::into(TokenError::MintCannotFreeze))?;
                    Self::validate_owner(
                        program_id,
                        &freeze_authority,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;
                    mint.freeze_authority = new_authority;
                }
                _ => {
                    return Err(TokenError::AuthorityTypeNotSupported.into());
                }
            }
            Mint::pack(mint, &mut account_info.data.borrow_mut())?;
        } else {
            return Err(ProgramError::InvalidArgument);
        }

        Ok(())
    }

    /// Processes a [`MintTo`](enum.TokenInstruction.html) instruction.
    pub fn process_mint_to(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        let destination_account_info = next_account_info(account_info_iter)?;
        let owner_info = next_account_info(account_info_iter)?;

        let mut destination_account = Account::unpack(&destination_account_info.data.borrow())?;
        if destination_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }

        if !Self::cmp_pubkeys(mint_info.key, &destination_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        let mut mint = Mint::unpack(&mint_info.data.borrow())?;
        if let Some(expected_decimals) = expected_decimals {
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        match mint.mint_authority {
            COption::Some(mint_authority) => Self::validate_owner(
                program_id,
                &mint_authority,
                owner_info,
                account_info_iter.as_slice(),
            )?,
            COption::None => return Err(TokenError::FixedSupply.into()),
        }

        if amount == 0 {
            Self::check_account_owner(program_id, mint_info)?;
            Self::check_account_owner(program_id, destination_account_info)?;
        }

        destination_account.amount = destination_account
            .amount
            .checked_add(amount)
            .ok_or(TokenError::Overflow)?;

        mint.supply = mint
            .supply
            .checked_add(amount)
            .ok_or(TokenError::Overflow)?;

        Account::pack(
            destination_account,
            &mut destination_account_info.data.borrow_mut(),
        )?;
        Mint::pack(mint, &mut mint_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`Burn`](enum.TokenInstruction.html) instruction.
    pub fn process_burn(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
        expected_decimals: Option<u8>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();

        let source_account_info = next_account_info(account_info_iter)?;
        let mint_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;
        let mut mint = Mint::unpack(&mint_info.data.borrow())?;

        if source_account.is_frozen() {
            return Err(TokenError::AccountFrozen.into());
        }
        if source_account.amount < amount {
            return Err(TokenError::InsufficientFunds.into());
        }
        if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        if let Some(expected_decimals) = expected_decimals {
            if expected_decimals != mint.decimals {
                return Err(TokenError::MintDecimalsMismatch.into());
            }
        }

        if source_account.owner != SYSTEM_PROGRAM_ID {
            match source_account.delegate {
                COption::Some(ref delegate) if Self::cmp_pubkeys(authority_info.key, delegate) => {
                    Self::validate_owner(
                        program_id,
                        delegate,
                        authority_info,
                        account_info_iter.as_slice(),
                    )?;

                    if source_account.delegated_amount < amount {
                        return Err(TokenError::InsufficientFunds.into());
                    }
                    source_account.delegated_amount = source_account
                        .delegated_amount
                        .checked_sub(amount)
                        .ok_or(TokenError::Overflow)?;
                    if source_account.delegated_amount == 0 {
                        source_account.delegate = COption::None;
                    }
                }
                _ => Self::validate_owner(
                    program_id,
                    &source_account.owner,
                    authority_info,
                    account_info_iter.as_slice(),
                )?,
            }
        }

        if amount == 0 {
            Self::check_account_owner(program_id, source_account_info)?;
            Self::check_account_owner(program_id, mint_info)?;
        }

        source_account.amount = source_account
            .amount
            .checked_sub(amount)
            .ok_or(TokenError::Overflow)?;
        mint.supply = mint
            .supply
            .checked_sub(amount)
            .ok_or(TokenError::Overflow)?;

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;
        Mint::pack(mint, &mut mint_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`CloseAccount`](enum.TokenInstruction.html) instruction.
    pub fn process_close_account(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let source_account_info = next_account_info(account_info_iter)?;
        let destination_account_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        if Self::cmp_pubkeys(source_account_info.key, destination_account_info.key) {
            return Err(ProgramError::InvalidAccountData);
        }

        let source_account = Account::unpack(&source_account_info.data.borrow())?;
        if source_account.amount != 0 {
            return Err(TokenError::NonNativeHasBalance.into());
        }

        let authority = source_account
            .close_authority
            .unwrap_or(source_account.owner);

        if source_account.owner != SYSTEM_PROGRAM_ID {
            Self::validate_owner(
                program_id,
                &authority,
                authority_info,
                account_info_iter.as_slice(),
            )?;
        }

        let destination_starting_lamports = destination_account_info.lamports();
        **destination_account_info.lamports.borrow_mut() = destination_starting_lamports
            .checked_add(source_account_info.lamports())
            .ok_or(TokenError::Overflow)?;

        **source_account_info.lamports.borrow_mut() = 0;

        delete_account(source_account_info)?;

        Ok(())
    }

    /// Processes a [`FreezeAccount`](enum.TokenInstruction.html) or a
    /// [`ThawAccount`](enum.TokenInstruction.html) instruction.
    pub fn process_toggle_freeze_account(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        freeze: bool,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let source_account_info = next_account_info(account_info_iter)?;
        let mint_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;

        let mut source_account = Account::unpack(&source_account_info.data.borrow())?;
        if freeze && source_account.is_frozen() || !freeze && !source_account.is_frozen() {
            return Err(TokenError::InvalidState.into());
        }
        if !Self::cmp_pubkeys(mint_info.key, &source_account.mint) {
            return Err(TokenError::MintMismatch.into());
        }

        let mint = Mint::unpack(&mint_info.data.borrow_mut())?;
        match mint.freeze_authority {
            COption::Some(authority) => Self::validate_owner(
                program_id,
                &authority,
                authority_info,
                account_info_iter.as_slice(),
            ),
            COption::None => Err(TokenError::MintCannotFreeze.into()),
        }?;

        source_account.state = if freeze {
            AccountState::Frozen
        } else {
            AccountState::Initialized
        };

        Account::pack(source_account, &mut source_account_info.data.borrow_mut())?;

        Ok(())
    }

    /// Processes a [`GetAccountDataSize`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_get_account_data_size(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        // make sure the mint is valid
        let mint_info = next_account_info(account_info_iter)?;
        Self::check_account_owner(program_id, mint_info)?;
        let _ = Mint::unpack(&mint_info.data.borrow())
            .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;
        set_return_data(&Account::LEN.to_le_bytes());
        Ok(())
    }

    /// Processes an [`InitializeImmutableOwner`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_initialize_immutable_owner(accounts: &[AccountInfo]) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let token_account_info = next_account_info(account_info_iter)?;
        let account = Account::unpack_unchecked(&token_account_info.data.borrow())?;
        if account.is_initialized() {
            return Err(TokenError::AlreadyInUse.into());
        }
        msg!("Please upgrade to SPL Token 2022 for immutable owner support");
        Ok(())
    }

    /// Processes an [`AmountToUiAmount`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_amount_to_ui_amount(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        amount: u64,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        Self::check_account_owner(program_id, mint_info)?;

        let mint = Mint::unpack(&mint_info.data.borrow_mut())
            .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;
        let ui_amount = amount_to_ui_amount_string_trimmed(amount, mint.decimals);

        set_return_data(&ui_amount.into_bytes());
        Ok(())
    }

    /// Processes an [`AmountToUiAmount`](enum.TokenInstruction.html)
    /// instruction
    pub fn process_ui_amount_to_amount(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        ui_amount: &str,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let mint_info = next_account_info(account_info_iter)?;
        Self::check_account_owner(program_id, mint_info)?;

        let mint = Mint::unpack(&mint_info.data.borrow_mut())
            .map_err(|_| Into::<ProgramError>::into(TokenError::InvalidMint))?;
        let amount = try_ui_amount_into_amount(ui_amount.to_string(), mint.decimals)?;

        set_return_data(&amount.to_le_bytes());
        Ok(())
    }

    /// Processes an [`Instruction`](enum.Instruction.html).
    pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], input: &[u8]) -> ProgramResult {
        let instruction = TokenInstruction::unpack(input)?;

        match instruction {
            TokenInstruction::InitializeMint {
                decimals,
                mint_authority,
                freeze_authority,
            } => {
                msg!("Instruction: InitializeMint");
                Self::process_initialize_mint(accounts, decimals, mint_authority, freeze_authority)
            }
            TokenInstruction::InitializeMint2 {
                decimals,
                mint_authority,
                freeze_authority,
            } => {
                msg!("Instruction: InitializeMint2");
                Self::process_initialize_mint2(accounts, decimals, mint_authority, freeze_authority)
            }
            TokenInstruction::InitializeAccount => {
                msg!("Instruction: InitializeAccount");
                Self::process_initialize_account(program_id, accounts)
            }
            TokenInstruction::InitializeAccount2 { owner } => {
                msg!("Instruction: InitializeAccount2");
                Self::process_initialize_account2(program_id, accounts, owner)
            }
            TokenInstruction::InitializeAccount3 { owner } => {
                msg!("Instruction: InitializeAccount3");
                Self::process_initialize_account3(program_id, accounts, owner)
            }
            TokenInstruction::InitializeMultisig { m } => {
                msg!("Instruction: InitializeMultisig");
                Self::process_initialize_multisig(accounts, m)
            }
            TokenInstruction::Transfer { amount } => {
                msg!("Instruction: Transfer");
                Self::process_transfer(program_id, accounts, amount, None)
            }
            TokenInstruction::Approve { amount } => {
                msg!("Instruction: Approve");
                Self::process_approve(program_id, accounts, amount, None)
            }
            TokenInstruction::Revoke => {
                msg!("Instruction: Revoke");
                Self::process_revoke(program_id, accounts)
            }
            TokenInstruction::SetAuthority {
                authority_type,
                new_authority,
            } => {
                msg!("Instruction: SetAuthority");
                Self::process_set_authority(program_id, accounts, authority_type, new_authority)
            }
            TokenInstruction::MintTo { amount } => {
                msg!("Instruction: MintTo");
                Self::process_mint_to(program_id, accounts, amount, None)
            }
            TokenInstruction::Burn { amount } => {
                msg!("Instruction: Burn");
                Self::process_burn(program_id, accounts, amount, None)
            }
            TokenInstruction::CloseAccount => {
                msg!("Instruction: CloseAccount");
                Self::process_close_account(program_id, accounts)
            }
            TokenInstruction::FreezeAccount => {
                msg!("Instruction: FreezeAccount");
                Self::process_toggle_freeze_account(program_id, accounts, true)
            }
            TokenInstruction::ThawAccount => {
                msg!("Instruction: ThawAccount");
                Self::process_toggle_freeze_account(program_id, accounts, false)
            }
            TokenInstruction::TransferChecked { amount, decimals } => {
                msg!("Instruction: TransferChecked");
                Self::process_transfer(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::ApproveChecked { amount, decimals } => {
                msg!("Instruction: ApproveChecked");
                Self::process_approve(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::MintToChecked { amount, decimals } => {
                msg!("Instruction: MintToChecked");
                Self::process_mint_to(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::BurnChecked { amount, decimals } => {
                msg!("Instruction: BurnChecked");
                Self::process_burn(program_id, accounts, amount, Some(decimals))
            }
            TokenInstruction::GetAccountDataSize => {
                msg!("Instruction: GetAccountDataSize");
                Self::process_get_account_data_size(program_id, accounts)
            }
            TokenInstruction::InitializeImmutableOwner => {
                msg!("Instruction: InitializeImmutableOwner");
                Self::process_initialize_immutable_owner(accounts)
            }
            TokenInstruction::AmountToUiAmount { amount } => {
                msg!("Instruction: AmountToUiAmount");
                Self::process_amount_to_ui_amount(program_id, accounts, amount)
            }
            TokenInstruction::UiAmountToAmount { ui_amount } => {
                msg!("Instruction: UiAmountToAmount");
                Self::process_ui_amount_to_amount(program_id, accounts, ui_amount)
            }
        }
    }

    /// Checks that the account is owned by the expected program
    pub fn check_account_owner(program_id: &Pubkey, account_info: &AccountInfo) -> ProgramResult {
        if !Self::cmp_pubkeys(program_id, account_info.owner) {
            Err(ProgramError::IncorrectProgramId)
        } else {
            Ok(())
        }
    }

    /// Checks two pubkeys for equality in a computationally cheap way using
    /// `sol_memcmp`
    pub fn cmp_pubkeys(a: &Pubkey, b: &Pubkey) -> bool {
        sol_memcmp(a.as_ref(), b.as_ref(), PUBKEY_BYTES) == 0
    }

    /// Validates owner(s) are present
    pub fn validate_owner(
        program_id: &Pubkey,
        expected_owner: &Pubkey,
        owner_account_info: &AccountInfo,
        signers: &[AccountInfo],
    ) -> ProgramResult {
        if !Self::cmp_pubkeys(expected_owner, owner_account_info.key) {
            return Err(TokenError::OwnerMismatch.into());
        }
        if Self::cmp_pubkeys(program_id, owner_account_info.owner)
            && owner_account_info.data_len() == Multisig::get_packed_len()
        {
            let multisig = Multisig::unpack(&owner_account_info.data.borrow())?;
            let mut num_signers = 0;
            let mut matched = [false; MAX_SIGNERS];
            for signer in signers.iter() {
                for (position, key) in multisig.signers[0..multisig.n as usize].iter().enumerate() {
                    if Self::cmp_pubkeys(key, signer.key) && !matched[position] {
                        if !signer.is_signer {
                            return Err(ProgramError::MissingRequiredSignature);
                        }
                        matched[position] = true;
                        num_signers += 1;
                    }
                }
            }
            if num_signers < multisig.m {
                return Err(ProgramError::MissingRequiredSignature);
            }
            return Ok(());
        } else if !owner_account_info.is_signer {
            return Err(ProgramError::MissingRequiredSignature);
        }
        Ok(())
    }
}

/// Helper function to mostly delete an account in a test environment.  We could
/// potentially muck around the bytes assuming that a vec is passed in, but that
/// would be more trouble than it's worth.
#[cfg(not(target_os = "solana"))]
fn delete_account(account_info: &AccountInfo) -> Result<(), ProgramError> {
    account_info.assign(&Pubkey::from_slice(b"11111111111111111111111111111111"));
    let mut account_data = account_info.data.borrow_mut();
    let data_len = account_data.len();
    arch_program::program_memory::sol_memset(*account_data, 0, data_len);
    Ok(())
}

/// Helper function to totally delete an account on-chain
#[cfg(target_os = "solana")]
fn delete_account(account_info: &AccountInfo) -> Result<(), ProgramError> {
    account_info.assign(&Pubkey::system_program());
    account_info.realloc(0, false)
}
