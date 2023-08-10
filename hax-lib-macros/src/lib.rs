use proc_macro::TokenStream;
use quote::{format_ident, quote};
// use syn::parse::Parse;
use proc_macro2::{Span, TokenStream as TokenStream2};
use syn::parse_macro_input;
use syn::Item;

const HAX_COMPILATION: &str = "hax_compilation";
const HAX_TOOL: &str = "_hax";

/// `passthrough_attribute!(NAME)` generates a proc-macro that expands
/// into the tool attribute `HAX_TOOL::NAME` when the cfg flag
/// `HAX_COMPILATION` is set.
macro_rules! passthrough_attribute {
    ($name:ident) => {
        #[proc_macro_attribute]
        pub fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
            let attr: TokenStream2 = attr.into();
            let item: TokenStream2 = item.into();
            let hax_compilation = format_ident!("{}", HAX_COMPILATION);
            let hax_tool = format_ident!("{}", HAX_TOOL);
            quote! {
                #[cfg_attr(#hax_compilation, #hax_tool::$name(#attr))]
                #item
            }
            .into()
        }
    };
}

passthrough_attribute!(skip);

#[proc_macro_attribute]
pub fn hax(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item: Item = {
        let item = item.clone();
        parse_macro_input!(item as Item)
    };

    struct AttrVisitor {}

    use syn::visit_mut;
    use syn::{Attribute, Expr, Ident, ItemFn, ItemStruct};
    use visit_mut::VisitMut;
    impl VisitMut for AttrVisitor {
        fn visit_item_mut(&mut self, item: &mut Item) {
            visit_mut::visit_item_mut(self, item);
            use syn::spanned::Spanned;
            let span = item.span();
            let mut extra: Vec<Item> = vec![];
            match item {
                Item::Struct(s) => {
                    let only_one_field = s.fields.len() == 1;
                    let idents: Vec<_> = s
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, field)| {
                            let ident = field.ident.clone().unwrap_or(if only_one_field {
                                format_ident!("x")
                            } else {
                                format_ident!("x{}", i)
                            });
                            (ident, field.ty.clone())
                        })
                        .collect();
                    for (i, field) in s.fields.iter_mut().enumerate() {
                        let prev = &idents[0..=i];
                        let refine: Option<(&mut Attribute, Expr)> =
                            field.attrs.iter_mut().find_map(|attr| {
                                if attr.path().is_ident("refine") {
                                    let payload = attr.parse_args().ok()?;
                                    Some((attr, payload))
                                } else {
                                    None
                                }
                            });
                        if let Some((attr, refine)) = refine {
                            let binders: TokenStream2 = prev
                                .iter()
                                .map(|(name, ty)| quote! {#name: #ty, })
                                .collect();
                            let hax_tool = format_ident!("{}", HAX_TOOL);
                            use uuid::Uuid;
                            let uuid = format!("{}", Uuid::new_v4().simple());
                            let hax_compilation = format_ident!("{}", HAX_COMPILATION);
                            *attr = syn::parse_quote! { #[cfg_attr(#hax_compilation, #hax_tool::uuid(#uuid))] };
                            extra.push(syn::parse_quote! {
                                #[cfg(#hax_compilation)]const _: () = {
                                    #[#hax_tool::associated_with(#uuid, refinement)]
                                    fn refinement(#binders) -> bool { #refine }
                                };
                            })
                        }
                    }
                }
                _ => (),
            }
            let extra: TokenStream2 = extra.iter().map(|extra| quote! {#extra}).collect();
            *item = Item::Verbatim(quote! {#extra #item});
        }
    }

    let mut v = AttrVisitor {};
    let mut item = item;
    v.visit_item_mut(&mut item);

    quote! { #item }.into()
}
