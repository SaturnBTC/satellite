use crate::{AccountField, AccountsStruct, Ty};
use heck::SnakeCase;
use quote::quote;
use std::str::FromStr;

// Generates the private `__client_accounts` mod implementation, containing
// a generated struct mapping 1-1 to the `Accounts` struct, except with
// `Pubkey`s as the types. This is generated for Rust *clients*.
pub fn generate(
    accs: &AccountsStruct,
    program_id: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let name = &accs.ident;
    let account_mod_name: proc_macro2::TokenStream = format!(
        "__client_accounts_{}",
        accs.ident.to_string().to_snake_case()
    )
    .parse()
    .unwrap();

    let account_struct_fields: Vec<proc_macro2::TokenStream> = accs
        .fields
        .iter()
        .map(|f: &AccountField| match f {
            AccountField::CompositeField(s) => {
                let name = &s.ident;
                let docs = if let Some(ref docs) = s.docs {
                    docs.iter()
                        .map(|docs_line| {
                            proc_macro2::TokenStream::from_str(&format!(
                                "#[doc = r#\"{docs_line}\"#]"
                            ))
                            .unwrap()
                        })
                        .collect()
                } else {
                    quote!()
                };
                let symbol: proc_macro2::TokenStream = format!(
                    "__client_accounts_{0}::{1}",
                    s.symbol.to_snake_case(),
                    s.symbol,
                )
                .parse()
                .unwrap();
                quote! {
                    #docs
                    pub #name: #symbol
                }
            }
            AccountField::Field(f) => {
                let name = &f.ident;
                let docs = if let Some(ref docs) = f.docs {
                    docs.iter()
                        .map(|docs_line| {
                            proc_macro2::TokenStream::from_str(&format!(
                                "#[doc = r#\"{docs_line}\"#]"
                            ))
                            .unwrap()
                        })
                        .collect()
                } else {
                    quote!()
                };
                if f.is_optional {
                    quote! {
                        #docs
                        pub #name: Option<Pubkey>
                    }
                } else {
                    quote! {
                        #docs
                        pub #name: Pubkey
                    }
                }
            }
        })
        .collect();

    let account_struct_metas: Vec<proc_macro2::TokenStream> = accs
        .fields
        .iter()
        .map(|f: &AccountField| match f {
            AccountField::CompositeField(s) => {
                let name = &s.ident;
                quote! {
                    account_metas.extend(self.#name.to_account_metas(None));
                }
            }
            AccountField::Field(f) => {
                let is_signer = match f.ty {
                    Ty::Signer => true,
                    _ => f.constraints.is_signer(),
                };
                let is_signer = match is_signer {
                    false => quote! {false},
                    true => quote! {true},
                };
                let meta = match f.constraints.is_mutable() {
                    false => quote! { satellite_lang::arch_program::account::AccountMeta::new_readonly },
                    true => quote! { satellite_lang::arch_program::account::AccountMeta::new },
                };
                let name = &f.ident;
                if f.is_optional {
                    quote! {
                        if let Some(#name) = &self.#name {
                            account_metas.push(#meta(*#name, #is_signer));
                        } else {
                            account_metas.push(satellite_lang::arch_program::account::AccountMeta::new_readonly(#program_id, false));
                        }
                    }
                } else {
                    quote! {
                        account_metas.push(#meta(self.#name, #is_signer));
                    }
                }
            }
        })
        .collect();
    // Re-export all composite account structs (i.e. other structs deriving
    // accounts embedded into this struct. Required because, these embedded
    // structs are *not* visible from the #[program] macro, which is responsible
    // for generating the `accounts` mod, which aggregates all the generated
    // accounts used for structs.
    let re_exports: Vec<proc_macro2::TokenStream> = {
        // First, dedup the exports.
        let mut re_exports = std::collections::HashSet::new();
        for f in accs.fields.iter().filter_map(|f: &AccountField| match f {
            AccountField::CompositeField(s) => Some(s),
            AccountField::Field(_) => None,
        }) {
            re_exports.insert(format!(
                "__client_accounts_{0}::{1}",
                f.symbol.to_snake_case(),
                f.symbol,
            ));
        }

        re_exports
            .iter()
            .map(|symbol: &String| {
                let symbol: proc_macro2::TokenStream = symbol.parse().unwrap();
                quote! {
                    pub use #symbol;
                }
            })
            .collect()
    };

    let struct_doc = proc_macro2::TokenStream::from_str(&format!(
        "#[doc = \" Generated client accounts for [`{name}`].\"]"
    ))
    .unwrap();

    quote! {
        /// An internal, Anchor generated module. This is used (as an
        /// implementation detail), to generate a struct for a given
        /// `#[derive(Accounts)]` implementation, where each field is a Pubkey,
        /// instead of an `AccountInfo`. This is useful for clients that want
        /// to generate a list of accounts, without explicitly knowing the
        /// order all the fields should be in.
        ///
        /// To access the struct in this module, one should use the sibling
        /// `accounts` module (also generated), which re-exports this.
        pub(crate) mod #account_mod_name {
            use super::*;
            use satellite_lang::prelude::borsh;
            #(#re_exports)*

            #struct_doc
            #[derive(satellite_lang::AnchorSerialize)]
            pub struct #name {
                #(#account_struct_fields),*
            }

            #[automatically_derived]
            impl satellite_lang::ToAccountMetas for #name {
                fn to_account_metas(&self, is_signer: Option<bool>) -> Vec<satellite_lang::arch_program::account::AccountMeta> {
                    let mut account_metas = vec![];

                    #(#account_struct_metas)*

                    account_metas
                }
            }
        }
    }
}
