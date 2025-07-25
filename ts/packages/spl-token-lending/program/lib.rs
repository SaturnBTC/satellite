// This file is autogenerated with https://github.com/acheroncrypto/native-to-anchor

use satellite_lang::prelude::*;

declare_id!("11111111111111111111111111111111");

#[program]
pub mod spl_token_lending {
    use super::*;

    pub fn init_lending_market(
        ctx: Context<InitLendingMarket>,
        owner: Pubkey,
        quote_currency: [u8; 32],
    ) -> Result<()> {
        Ok(())
    }

    pub fn set_lending_market_owner(
        ctx: Context<SetLendingMarketOwner>,
        new_owner: Pubkey,
    ) -> Result<()> {
        Ok(())
    }

    pub fn init_reserve(
        ctx: Context<InitReserve>,
        liquidity_amount: u64,
        config: ReserveConfig,
    ) -> Result<()> {
        Ok(())
    }

    pub fn refresh_reserve(ctx: Context<RefreshReserve>) -> Result<()> {
        Ok(())
    }

    pub fn deposit_reserve_liquidity(
        ctx: Context<DepositReserveLiquidity>,
        liquidity_amount: u64,
    ) -> Result<()> {
        Ok(())
    }

    pub fn redeem_reserve_collateral(
        ctx: Context<RedeemReserveCollateral>,
        collateral_amount: u64,
    ) -> Result<()> {
        Ok(())
    }

    pub fn init_obligation(ctx: Context<InitObligation>) -> Result<()> {
        Ok(())
    }

    pub fn refresh_obligation(ctx: Context<RefreshObligation>) -> Result<()> {
        Ok(())
    }

    pub fn deposit_obligation_collateral(
        ctx: Context<DepositObligationCollateral>,
        collateral_amount: u64,
    ) -> Result<()> {
        Ok(())
    }

    pub fn withdraw_obligation_collateral(
        ctx: Context<WithdrawObligationCollateral>,
        collateral_amount: u64,
    ) -> Result<()> {
        Ok(())
    }

    pub fn borrow_obligation_liquidity(
        ctx: Context<BorrowObligationLiquidity>,
        liquidity_amount: u64,
    ) -> Result<()> {
        Ok(())
    }

    pub fn repay_obligation_liquidity(
        ctx: Context<RepayObligationLiquidity>,
        liquidity_amount: u64,
    ) -> Result<()> {
        Ok(())
    }

    pub fn liquidate_obligation(
        ctx: Context<LiquidateObligation>,
        liquidity_amount: u64,
    ) -> Result<()> {
        Ok(())
    }

    pub fn flash_loan(ctx: Context<FlashLoan>, amount: u64) -> Result<()> {
        Ok(())
    }
}

#[derive(Accounts)]
pub struct InitLendingMarket<'info> {
    #[account(mut)]
    lending_market: AccountInfo<'info>,
    rent: Sysvar<'info, Rent>,
    token_program: Program<'info, Token>,
    oracle_program: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct SetLendingMarketOwner<'info> {
    #[account(mut)]
    lending_market: AccountInfo<'info>,
    lending_market_owner: Signer<'info>,
}

#[derive(Accounts)]
pub struct InitReserve<'info> {
    #[account(mut)]
    source_liquidity: AccountInfo<'info>,
    #[account(mut)]
    destination_collateral: AccountInfo<'info>,
    #[account(mut)]
    reserve: AccountInfo<'info>,
    reserve_liquidity_mint: AccountInfo<'info>,
    #[account(mut)]
    reserve_liquidity_supply: AccountInfo<'info>,
    #[account(mut)]
    reserve_liquidity_fee_receiver: AccountInfo<'info>,
    #[account(mut)]
    reserve_collateral_mint: AccountInfo<'info>,
    #[account(mut)]
    reserve_collateral_supply: AccountInfo<'info>,
    pyth_product: AccountInfo<'info>,
    pyth_price: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    lending_market_authority: AccountInfo<'info>,
    lending_market_owner: Signer<'info>,
    user_transfer_authority: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    rent: Sysvar<'info, Rent>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct RefreshReserve<'info> {
    #[account(mut)]
    reserve: AccountInfo<'info>,
    reserve_liquidity_oracle: AccountInfo<'info>,
    clock: Sysvar<'info, Clock>,
}

#[derive(Accounts)]
pub struct DepositReserveLiquidity<'info> {
    #[account(mut)]
    source_liquidity: AccountInfo<'info>,
    #[account(mut)]
    destination_collateral: AccountInfo<'info>,
    #[account(mut)]
    reserve: AccountInfo<'info>,
    #[account(mut)]
    reserve_liquidity_supply: AccountInfo<'info>,
    #[account(mut)]
    reserve_collateral_mint: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    lending_market_authority: AccountInfo<'info>,
    user_transfer_authority: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct RedeemReserveCollateral<'info> {
    #[account(mut)]
    source_collateral: AccountInfo<'info>,
    #[account(mut)]
    destination_liquidity: AccountInfo<'info>,
    #[account(mut)]
    reserve: AccountInfo<'info>,
    #[account(mut)]
    reserve_collateral_mint: AccountInfo<'info>,
    #[account(mut)]
    reserve_liquidity_supply: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    lending_market_authority: AccountInfo<'info>,
    user_transfer_authority: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct InitObligation<'info> {
    #[account(mut)]
    obligation: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    obligation_owner: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    rent: Sysvar<'info, Rent>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct RefreshObligation<'info> {
    #[account(mut)]
    obligation: AccountInfo<'info>,
    clock: Sysvar<'info, Clock>,
    // optional_pubkey: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct DepositObligationCollateral<'info> {
    #[account(mut)]
    source_collateral: AccountInfo<'info>,
    #[account(mut)]
    destination_collateral: AccountInfo<'info>,
    deposit_reserve: AccountInfo<'info>,
    #[account(mut)]
    obligation: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    obligation_owner: Signer<'info>,
    user_transfer_authority: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct WithdrawObligationCollateral<'info> {
    #[account(mut)]
    source_collateral: AccountInfo<'info>,
    #[account(mut)]
    destination_collateral: AccountInfo<'info>,
    withdraw_reserve: AccountInfo<'info>,
    #[account(mut)]
    obligation: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    lending_market_authority: AccountInfo<'info>,
    obligation_owner: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct BorrowObligationLiquidity<'info> {
    #[account(mut)]
    source_liquidity: AccountInfo<'info>,
    #[account(mut)]
    destination_liquidity: AccountInfo<'info>,
    #[account(mut)]
    borrow_reserve: AccountInfo<'info>,
    #[account(mut)]
    borrow_reserve_liquidity_fee_receiver: AccountInfo<'info>,
    #[account(mut)]
    obligation: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    lending_market_authority: AccountInfo<'info>,
    obligation_owner: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    token_program: Program<'info, Token>,
    // #[account(mut)]
    // optional_host_fee_receiver: AccountInfo<'info>,
}

#[derive(Accounts)]
pub struct RepayObligationLiquidity<'info> {
    #[account(mut)]
    source_liquidity: AccountInfo<'info>,
    #[account(mut)]
    destination_liquidity: AccountInfo<'info>,
    #[account(mut)]
    repay_reserve: AccountInfo<'info>,
    #[account(mut)]
    obligation: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    user_transfer_authority: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct LiquidateObligation<'info> {
    #[account(mut)]
    source_liquidity: AccountInfo<'info>,
    #[account(mut)]
    destination_collateral: AccountInfo<'info>,
    #[account(mut)]
    repay_reserve: AccountInfo<'info>,
    #[account(mut)]
    repay_reserve_liquidity_supply: AccountInfo<'info>,
    withdraw_reserve: AccountInfo<'info>,
    #[account(mut)]
    withdraw_reserve_collateral_supply: AccountInfo<'info>,
    #[account(mut)]
    obligation: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    lending_market_authority: AccountInfo<'info>,
    user_transfer_authority: Signer<'info>,
    clock: Sysvar<'info, Clock>,
    token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct FlashLoan<'info> {
    #[account(mut)]
    source_liquidity: AccountInfo<'info>,
    #[account(mut)]
    destination_liquidity: AccountInfo<'info>,
    #[account(mut)]
    reserve: AccountInfo<'info>,
    #[account(mut)]
    reserve_liquidity_fee_receiver: AccountInfo<'info>,
    #[account(mut)]
    host_fee_receiver: AccountInfo<'info>,
    lending_market: AccountInfo<'info>,
    lending_market_authority: AccountInfo<'info>,
    token_program: Program<'info, Token>,
    flash_loan_receiver_program: AccountInfo<'info>,
}

#[account]
pub struct Obligation {
    /// Version of the struct
    pub version: u8,
    /// Last update to collateral, liquidity, or their market values
    pub last_update: LastUpdate,
    /// Lending market address
    pub lending_market: Pubkey,
    /// Owner authority which can borrow liquidity
    pub owner: Pubkey,
    /// Deposited collateral for the obligation, unique by deposit reserve address
    pub deposits: Vec<ObligationCollateral>,
    /// Borrowed liquidity for the obligation, unique by borrow reserve address
    pub borrows: Vec<ObligationLiquidity>,
    /// Market value of deposits
    pub deposited_value: Decimal,
    /// Market value of borrows
    pub borrowed_value: Decimal,
    /// The maximum borrow value at the weighted average loan to value ratio
    pub allowed_borrow_value: Decimal,
    /// The dangerous borrow value at the weighted average liquidation threshold
    pub unhealthy_borrow_value: Decimal,
}

#[account]
pub struct LendingMarket {
    /// Version of lending market
    pub version: u8,
    /// Bump seed for derived authority address
    pub bump_seed: u8,
    /// Owner authority which can add new reserves
    pub owner: Pubkey,
    /// Currency market prices are quoted in
    /// e.g. "USD" null padded (`*b"USD\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"`) or a SPL token mint pubkey
    pub quote_currency: [u8; 32],
    /// Token program id
    pub token_program_id: Pubkey,
    /// Oracle (Pyth) program id
    pub oracle_program_id: Pubkey,
}

#[account]
pub struct Reserve {
    /// Version of the struct
    pub version: u8,
    /// Last slot when supply and rates updated
    pub last_update: LastUpdate,
    /// Lending market address
    pub lending_market: Pubkey,
    /// Reserve liquidity
    pub liquidity: ReserveLiquidity,
    /// Reserve collateral
    pub collateral: ReserveCollateral,
    /// Reserve configuration values
    pub config: ReserveConfig,
}

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct LastUpdate {
    /// Last slot when updated
    pub slot: u64,
    /// True when marked stale, false when slot updated
    pub stale: bool,
}

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct Decimal(pub U192);

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct ObligationCollateral {
    /// Reserve collateral is deposited to
    pub deposit_reserve: Pubkey,
    /// Amount of collateral deposited
    pub deposited_amount: u64,
    /// Collateral market value in quote currency
    pub market_value: Decimal,
}

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct ObligationLiquidity {
    /// Reserve liquidity is borrowed from
    pub borrow_reserve: Pubkey,
    /// Borrow rate used for calculating interest
    pub cumulative_borrow_rate_wads: Decimal,
    /// Amount of liquidity borrowed plus interest
    pub borrowed_amount_wads: Decimal,
    /// Liquidity market value in quote currency
    pub market_value: Decimal,
}

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct ReserveLiquidity {
    /// Reserve liquidity mint address
    pub mint_pubkey: Pubkey,
    /// Reserve liquidity mint decimals
    pub mint_decimals: u8,
    /// Reserve liquidity supply address
    pub supply_pubkey: Pubkey,
    /// Reserve liquidity fee receiver address
    pub fee_receiver: Pubkey,
    /// Reserve liquidity oracle account
    pub oracle_pubkey: Pubkey,
    /// Reserve liquidity available
    pub available_amount: u64,
    /// Reserve liquidity borrowed
    pub borrowed_amount_wads: Decimal,
    /// Reserve liquidity cumulative borrow rate
    pub cumulative_borrow_rate_wads: Decimal,
    /// Reserve liquidity market price in quote currency
    pub market_price: Decimal,
}

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct ReserveCollateral {
    /// Reserve collateral mint address
    pub mint_pubkey: Pubkey,
    /// Reserve collateral mint supply, used for exchange rate
    pub mint_total_supply: u64,
    /// Reserve collateral supply address
    pub supply_pubkey: Pubkey,
}

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct ReserveFees {
    /// Fee assessed on `BorrowObligationLiquidity`, expressed as a Wad.
    /// Must be between 0 and 10^18, such that 10^18 = 1.  A few examples for
    /// clarity:
    /// 1% = 10_000_000_000_000_000
    /// 0.01% (1 basis point) = 100_000_000_000_000
    /// 0.00001% (Aave borrow fee) = 100_000_000_000
    pub borrow_fee_wad: u64,
    /// Fee for flash loan, expressed as a Wad.
    /// 0.3% (Aave flash loan fee) = 3_000_000_000_000_000
    pub flash_loan_fee_wad: u64,
    /// Amount of fee going to host account, if provided in liquidate and repay
    pub host_fee_percentage: u8,
}

#[derive(AnchorSerialize, AnchorDeserialize)]
pub struct ReserveConfig {
    /// Optimal utilization rate, as a percentage
    pub optimal_utilization_rate: u8,
    /// Target ratio of the value of borrows to deposits, as a percentage
    /// 0 if use as collateral is disabled
    pub loan_to_value_ratio: u8,
    /// Bonus a liquidator gets when repaying part of an unhealthy obligation, as a percentage
    pub liquidation_bonus: u8,
    /// Loan to value ratio at which an obligation can be liquidated, as a percentage
    pub liquidation_threshold: u8,
    /// Min borrow APY
    pub min_borrow_rate: u8,
    /// Optimal (utilization) borrow APY
    pub optimal_borrow_rate: u8,
    /// Max borrow APY
    pub max_borrow_rate: u8,
    /// Program owner fees assessed, separate from gains due to interest accrual
    pub fees: ReserveFees,
}

#[error_code]
pub enum LendingError {
    // 0
    /// Invalid instruction data passed in.
    #[msg("Failed to unpack instruction data")]
    InstructionUnpackError,
    /// The account cannot be initialized because it is already in use.
    #[msg("Account is already initialized")]
    AlreadyInitialized,
    /// Lamport balance below rent-exempt threshold.
    #[msg("Lamport balance below rent-exempt threshold")]
    NotRentExempt,
    /// The program address provided doesn't match the value generated by the program.
    #[msg("Market authority is invalid")]
    InvalidMarketAuthority,
    /// Expected a different market owner
    #[msg("Market owner is invalid")]
    InvalidMarketOwner,

    // 5
    /// The owner of the input isn't set to the program address generated by the program.
    #[msg("Input account owner is not the program address")]
    InvalidAccountOwner,
    /// The owner of the account input isn't set to the correct token program id.
    #[msg("Input token account is not owned by the correct token program id")]
    InvalidTokenOwner,
    /// Expected an SPL Token account
    #[msg("Input token account is not valid")]
    InvalidTokenAccount,
    /// Expected an SPL Token mint
    #[msg("Input token mint account is not valid")]
    InvalidTokenMint,
    /// Expected a different SPL Token program
    #[msg("Input token program account is not valid")]
    InvalidTokenProgram,

    // 10
    /// Invalid amount, must be greater than zero
    #[msg("Input amount is invalid")]
    InvalidAmount,
    /// Invalid config value
    #[msg("Input config value is invalid")]
    InvalidConfig,
    /// Invalid config value
    #[msg("Input account must be a signer")]
    InvalidSigner,
    /// Invalid account input
    #[msg("Invalid account input")]
    InvalidAccountInput,
    /// Math operation overflow
    #[msg("Math operation overflow")]
    MathOverflow,

    // 15
    /// Token initialize mint failed
    #[msg("Token initialize mint failed")]
    TokenInitializeMintFailed,
    /// Token initialize account failed
    #[msg("Token initialize account failed")]
    TokenInitializeAccountFailed,
    /// Token transfer failed
    #[msg("Token transfer failed")]
    TokenTransferFailed,
    /// Token mint to failed
    #[msg("Token mint to failed")]
    TokenMintToFailed,
    /// Token burn failed
    #[msg("Token burn failed")]
    TokenBurnFailed,

    // 20
    /// Insufficient liquidity available
    #[msg("Insufficient liquidity available")]
    InsufficientLiquidity,
    /// This reserve's collateral cannot be used for borrows
    #[msg("Input reserve has collateral disabled")]
    ReserveCollateralDisabled,
    /// Reserve state stale
    #[msg("Reserve state needs to be refreshed")]
    ReserveStale,
    /// Withdraw amount too small
    #[msg("Withdraw amount too small")]
    WithdrawTooSmall,
    /// Withdraw amount too large
    #[msg("Withdraw amount too large")]
    WithdrawTooLarge,

    // 25
    /// Borrow amount too small
    #[msg("Borrow amount too small to receive liquidity after fees")]
    BorrowTooSmall,
    /// Borrow amount too large
    #[msg("Borrow amount too large for deposited collateral")]
    BorrowTooLarge,
    /// Repay amount too small
    #[msg("Repay amount too small to transfer liquidity")]
    RepayTooSmall,
    /// Liquidation amount too small
    #[msg("Liquidation amount too small to receive collateral")]
    LiquidationTooSmall,
    /// Cannot liquidate healthy obligations
    #[msg("Cannot liquidate healthy obligations")]
    ObligationHealthy,

    // 30
    /// Obligation state stale
    #[msg("Obligation state needs to be refreshed")]
    ObligationStale,
    /// Obligation reserve limit exceeded
    #[msg("Obligation reserve limit exceeded")]
    ObligationReserveLimit,
    /// Expected a different obligation owner
    #[msg("Obligation owner is invalid")]
    InvalidObligationOwner,
    /// Obligation deposits are empty
    #[msg("Obligation deposits are empty")]
    ObligationDepositsEmpty,
    /// Obligation borrows are empty
    #[msg("Obligation borrows are empty")]
    ObligationBorrowsEmpty,

    // 35
    /// Obligation deposits have zero value
    #[msg("Obligation deposits have zero value")]
    ObligationDepositsZero,
    /// Obligation borrows have zero value
    #[msg("Obligation borrows have zero value")]
    ObligationBorrowsZero,
    /// Invalid obligation collateral
    #[msg("Invalid obligation collateral")]
    InvalidObligationCollateral,
    /// Invalid obligation liquidity
    #[msg("Invalid obligation liquidity")]
    InvalidObligationLiquidity,
    /// Obligation collateral is empty
    #[msg("Obligation collateral is empty")]
    ObligationCollateralEmpty,

    // 40
    /// Obligation liquidity is empty
    #[msg("Obligation liquidity is empty")]
    ObligationLiquidityEmpty,
    /// Negative interest rate
    #[msg("Interest rate is negative")]
    NegativeInterestRate,
    /// Oracle config is invalid
    #[msg("Input oracle config is invalid")]
    InvalidOracleConfig,
    /// Expected a different flash loan receiver program
    #[msg("Input flash loan receiver program account is not valid")]
    InvalidFlashLoanReceiverProgram,
    /// Not enough liquidity after flash loan
    #[msg("Not enough liquidity after flash loan")]
    NotEnoughLiquidityAfterFlashLoan,
    // 45
}
