use satellite_lang_idl::types::Idl;
use heck::CamelCase;
use quote::{format_ident, quote};

use super::common::{convert_idl_type_to_syn_type, gen_accounts_common};

pub fn gen_cpi_mod(idl: &Idl) -> proc_macro2::TokenStream {
    let cpi_instructions = gen_cpi_instructions(idl);
    let cpi_return_type = gen_cpi_return_type();
    let cpi_accounts_mod = gen_cpi_accounts_mod(idl);

    quote! {
        /// Cross program invocation (CPI) helpers.
        pub mod cpi {
            use super::*;

            #cpi_instructions
            #cpi_return_type
            #cpi_accounts_mod
        }
    }
}

fn gen_cpi_instructions(idl: &Idl) -> proc_macro2::TokenStream {
    let ixs = idl.instructions.iter().map(|ix| {
        let method_name = format_ident!("{}", ix.name);
        let accounts_ident = format_ident!("{}", ix.name.to_camel_case());

        let accounts_generic = if ix.accounts.is_empty() {
           quote!()
        } else {
            quote!(<'info>)
        };

        let args = ix.args.iter().map(|arg| {
            let name = format_ident!("{}", arg.name);
            let ty = convert_idl_type_to_syn_type(&arg.ty);
            quote! { #name: #ty }
        });

        let arg_value = if ix.args.is_empty() {
            quote! { #accounts_ident }
        } else {
            let fields= ix.args.iter().map(|arg| format_ident!("{}", arg.name));
            quote! {
                #accounts_ident {
                    #(#fields),*
                }
            }
        };

        let (ret_type, ret_value) = match ix.returns.as_ref() {
            Some(ty) => {
                let ty = convert_idl_type_to_syn_type(ty);
                (
                    quote! { satellite_lang::Result<Return::<#ty>> },
                    quote! { Ok(Return::<#ty> { phantom: std::marker::PhantomData }) },
                )
            },
            None => (
                quote! { satellite_lang::Result<()> },
                quote! { Ok(()) },
            )
        };

        quote! {
            pub fn #method_name<'a, 'b, 'c, 'info>(
                ctx: satellite_lang::context::CpiContext<'a, 'b, 'c, 'info, accounts::#accounts_ident #accounts_generic>,
                #(#args),*
            ) -> #ret_type {
                let ix = {
                    let ix = internal::args::#arg_value;
                    let mut data = Vec::with_capacity(256);
                    data.extend_from_slice(internal::args::#accounts_ident::DISCRIMINATOR);
                    AnchorSerialize::serialize(&ix, &mut data)
                        .map_err(|_| satellite_lang::error::ErrorCode::InstructionDidNotSerialize)?;

                    let accounts = ctx.to_account_metas(None);
                    satellite_lang::arch_program::instruction::Instruction {
                        program_id: ctx.program.key(),
                        accounts,
                        data,
                    }
                };

                let mut acc_infos = ctx.to_account_infos();
                satellite_lang::arch_program::program::invoke_signed(
                    &ix,
                    &acc_infos,
                    ctx.signer_seeds,
                ).map_or_else(
                    |e| Err(Into::into(e)),
                    |_| { #ret_value }
                )
            }
        }
    });

    quote! {
        #(#ixs)*
    }
}

fn gen_cpi_return_type() -> proc_macro2::TokenStream {
    quote! {
        pub struct Return<T> {
            phantom: std::marker::PhantomData<T>
        }

        impl<T: AnchorDeserialize> Return<T> {
            pub fn get(&self) -> T {
                let (_key, data) = satellite_lang::arch_program::program::get_return_data().unwrap();
                T::try_from_slice(&data).unwrap()
            }
        }
    }
}

fn gen_cpi_accounts_mod(idl: &Idl) -> proc_macro2::TokenStream {
    gen_accounts_common(idl, "cpi_client")
}
