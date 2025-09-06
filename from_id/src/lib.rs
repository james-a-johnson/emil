use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::{Data, DeriveInput, parse_macro_input};

#[proc_macro_derive(FromId)]
pub fn derive_from_id(items: TokenStream) -> TokenStream {
    let data = parse_macro_input!(items as DeriveInput);
    let name = data.ident;
    let en = match data.data {
        Data::Enum(e) => e,
        Data::Struct(s) => {
            return quote_spanned! { s.struct_token.span => compile_error!("Only support enums") }
                .into();
        }
        Data::Union(u) => {
            return quote_spanned! { u.union_token.span => compile_error!("Only support enums") }
                .into();
        }
    };

    let variants = en.variants.clone().into_iter().map(|var| var.ident);
    let discriminants = en
        .variants
        .into_iter()
        .map(|var| var.discriminant.unwrap().1);

    let toks = quote! {
        impl TryFrom<u32> for #name {
            type Error = u32;

            fn try_from(id: u32) -> Result<Self, u32> {
                match id {
                    #(#discriminants => Ok(Self::#variants),)*
                    _ => Err(id),
                }
            }
        }
    };
    toks.into()
}
