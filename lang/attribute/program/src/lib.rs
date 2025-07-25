extern crate proc_macro;

mod declare_program;

use declare_program::DeclareProgram;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, AttributeArgs, NestedMeta, Meta, ItemMod};

/// The `#[program]` attribute defines the module containing all instruction
/// handlers defining all entries into a Solana program.
#[proc_macro_attribute]
pub fn program(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    // Parse the attribute arguments, looking for an optional `btc_tx(...)` section.
    let args_parsed = parse_macro_input!(args as AttributeArgs);

    // Parse the incoming module so we can attach a synthetic attribute.
    let mut program_mod = parse_macro_input!(input as ItemMod);

    // Extract btc_tx nested list if present.
    for nested in args_parsed {
        match nested {
            NestedMeta::Meta(Meta::List(list)) if list.path.is_ident("btc_tx") => {
                let nested = &list.nested;
                // `nested` contains arguments like `max_inputs_to_sign = 4, ...`
                let cfg_attr: syn::Attribute = syn::parse_quote! {
                    #[btc_tx_cfg( #nested )]
                };
                program_mod.attrs.push(cfg_attr);
            }
            _ => {
                // Ignore or emit error for unsupported meta
            }
        }
    }

    // Convert modified module back into tokens and let anchor_syn handle the heavy lifting.
    let program_tokens = quote! { #program_mod };
    match syn::parse2::<anchor_syn::Program>(program_tokens) {
        Ok(p) => p.to_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Declare an external program based on its IDL.
///
/// The IDL of the program must exist in a directory named `idls`. This directory can be at any
/// depth, e.g. both inside the program's directory (`<PROGRAM_DIR>/idls`) and inside Anchor
/// workspace root directory (`<PROGRAM_DIR>/../../idls`) are valid.
///
/// # Usage
///
/// ```rs
/// declare_program!(program_name);
/// ```
///
/// This generates a module named `program_name` that can be used to interact with the program
/// without having to add the program's crate as a dependency.
///
/// Both on-chain and off-chain usage is supported.
///
/// Use `cargo doc --open` to see the generated modules and their documentation.
///
/// # Note
///
/// Re-defining the same program to use the same definitions should be avoided since this results
/// in a larger binary size.
///
/// A program should only be defined once. If you have multiple programs that depend on the same
/// definition, you should consider creating a separate crate for the external program definition
/// and reusing it in your programs.
///
/// # Example
///
/// A full on-chain CPI usage example can be found [here].
///
/// [here]: https://github.com/coral-xyz/anchor/tree/v0.31.1/tests/declare-program
#[proc_macro]
pub fn declare_program(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    parse_macro_input!(input as DeclareProgram)
        .to_token_stream()
        .into()
}

/// The `#[interface]` attribute is used to mark an instruction as belonging
/// to an interface implementation, thus transforming its discriminator to the
/// proper bytes for that interface instruction.
///
/// # Example
///
/// ```rust,ignore
/// use satellite_lang::prelude::*;
///
/// // SPL Transfer Hook Interface: `Execute` instruction.
/// //
/// // This instruction is invoked by Token-2022 when a transfer occurs,
/// // if a mint has specified this program as its transfer hook.
/// #[interface(spl_transfer_hook_interface::execute)]
/// pub fn execute_transfer(ctx: Context<Execute>, amount: u64) -> Result<()> {
///     // Check that all extra accounts were provided
///     let data = ctx.accounts.extra_metas_account.try_borrow_data()?;
///     ExtraAccountMetaList::check_account_infos::<ExecuteInstruction>(
///         &ctx.accounts.to_account_infos(),
///         &TransferHookInstruction::Execute { amount }.pack(),
///         &ctx.program_id,
///         &data,
///     )?;
///
///     // Or maybe perform some custom logic
///     if ctx.accounts.token_metadata.mint != ctx.accounts.token_account.mint {
///         return Err(ProgramError::IncorrectAccount);
///     }
///
///     Ok(())
/// }
/// ```
#[cfg(feature = "interface-instructions")]
#[deprecated(
    since = "0.31.1",
    note = "Use `#[instruction(discriminator = <EXPR>)]` instead.
    See examples in https://github.com/coral-xyz/anchor/tree/v0.31.1/tests/spl/transfer-hook"
)]
#[proc_macro_attribute]
pub fn interface(
    _args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    // This macro itself is a no-op, but must be defined as a proc-macro
    // attribute to be used on a function as the `#[interface]` attribute.
    //
    // The `#[program]` macro will detect this attribute and transform the
    // discriminator.
    input
}

/// This attribute is used to override the Anchor defaults of program instructions.
///
/// # Arguments
///
/// - `discriminator`: Override the default 8-byte discriminator
///
///     **Usage:** `discriminator = <CONST_EXPR>`
///
///     All constant expressions are supported.
///
///     **Examples:**
///
///     - `discriminator = 1` (shortcut for `[1]`)
///     - `discriminator = [1, 2, 3, 4]`
///     - `discriminator = b"hi"`
///     - `discriminator = MY_DISC`
///     - `discriminator = get_disc(...)`
///
/// # Example
///
/// ```ignore
/// use satellite_lang::prelude::*;
///
/// declare_id!("CustomDiscriminator111111111111111111111111");
///
/// #[program]
/// pub mod custom_discriminator {
///     use super::*;
///
///     #[instruction(discriminator = [1, 2, 3, 4])]
///     pub fn my_ix(_ctx: Context<MyIx>) -> Result<()> {
///         Ok(())
///     }
/// }
///
/// #[derive(Accounts)]
/// pub struct MyIx<'info> {
///     pub signer: Signer<'info>,
/// }
/// ```
#[proc_macro_attribute]
pub fn instruction(
    _args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    // This macro itself is a no-op, but the `#[program]` macro will detect this attribute and use
    // the arguments to transform the instruction.
    input
}
