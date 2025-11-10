# Solana → Arch Migration

## 1) Dependency swaps (Cargo.toml + imports)

**Cargo.toml**

```toml
[dependencies]
# Solana → Arch
- solana_program = "x.y"
+ arch_program = "x.y"

- anchor-lang = "x.y"
+ satellite-lang = "x.y"

- anchor-spl = "x.y"
+ satellite-apl = "x.y"

- spl-token = "x.y"
+ apl-token = "x.y"
```

**Rust imports**

```rust
- use solana_program;
+ use arch_program;

- use anchor-lang;
+ use satellite-lang;

- use anchor-spl;
+ use satellite-apl;

- use spl-token;
+ use apl-token;
```

---

## 2) Token interfaces → classic types (no token extensions yet)

`satellite-apl` does **not** support Token Extensions. Replace `Interface`, `InterfaceAccount`, and `TokenInterface` with the classic account types and comment out/replace all token 2022 usage.

**Before (Anchor on Solana)**

```rust
#[derive(Accounts)]
pub struct Transfer<'info> {
    #[account(mut)]
    pub from: InterfaceAccount<'info, TokenAccountInterface>,
    #[account(mut)]
    pub to: InterfaceAccount<'info, TokenAccountInterface>,
    pub token_program: Interface<'info, TokenInterface>,
}
```

**After (Satellite on Arch)**

```rust
#[derive(Accounts)]
pub struct Transfer<'info> {
    #[account(mut)]
    pub from: Account<'info, TokenAccount>,
    #[account(mut)]
    pub to: Account<'info, TokenAccount>,
    pub token_program: Program<'info, Token>,
}
```

---

## 3) Remove Sysvar account types from contexts

Satellite exposes sysvars via syscalls—**do not** pass them as accounts.

**Before**

```rust
#[derive(Accounts)]
pub struct DoThing<'info> {
    pub rent: Sysvar<'info, Rent>,
    pub clock: Sysvar<'info, Clock>,
}
```

**After**

```rust
#[derive(Accounts)]
pub struct DoThing<'info> {
    // no sysvar accounts here
}
```

---

## 4) Rent + Clock APIs

Replace Solana’s rent and clock access with Arch equivalents.

**Rent:**

```rust
- let lamports = Rent::get()?.minimum_balance(data_len);
+ use arch_program::rent;
+ let lamports: u64 = rent::minimum_rent(data_len);
```

**Clock:**

```rust
- let clock = Clock::get()?;
- let now = clock.unix_timestamp;
+ use arch_program::get_clock;
+ let clock = get_clock();
+ let now = clock.unix_timestamp;
```

## 5) Remove or replace leftover Solana-specific programs such as memo_program
