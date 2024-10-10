mod hax_paths;

use hax_paths::*;
use proc_macro::TokenStream;
use quote::quote;
use syn::{visit_mut::VisitMut, *};

macro_rules! identity_proc_macro_attribute {
    ($($name:ident,)*) => {
        $(
            #[proc_macro_attribute]
            pub fn $name(_attr: TokenStream, item: TokenStream) -> TokenStream {
                item
            }
        )*
    }
}

identity_proc_macro_attribute!(
    fstar_options,
    fstar_verification_status,
    include,
    exclude,
    requires,
    ensures,
    pv_handwritten,
    pv_constructor,
    protocol_messages,
    process_init,
    process_write,
    process_read,
    opaque_type,
    refinement_type,
    fstar_replace,
    coq_replace,
    proverif_replace,
    fstar_before,
    coq_before,
    proverif_before,
    fstar_after,
    coq_after,
    proverif_after,
);

#[proc_macro]
pub fn fstar_expr(_payload: TokenStream) -> TokenStream {
    quote! { () }.into()
}
#[proc_macro]
pub fn coq_expr(_payload: TokenStream) -> TokenStream {
    quote! { () }.into()
}
#[proc_macro]
pub fn proverif_expr(_payload: TokenStream) -> TokenStream {
    quote! { () }.into()
}

#[proc_macro_attribute]
pub fn lemma(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    quote! {}.into()
}

fn unsafe_expr() -> TokenStream {
    quote! { ::std::compile_error!("`hax_lib::unsafe_expr` has no meaning outside of hax extraction, please use it solely on hax only places.") }.into()
}

#[proc_macro]
pub fn fstar_unsafe_expr(_payload: TokenStream) -> TokenStream {
    unsafe_expr()
}
#[proc_macro]
pub fn coq_unsafe_expr(_payload: TokenStream) -> TokenStream {
    unsafe_expr()
}
#[proc_macro]
pub fn proverif_unsafe_expr(_payload: TokenStream) -> TokenStream {
    unsafe_expr()
}

fn not_hax_attribute(attr: &syn::Attribute) -> bool {
    if let Meta::List(ml) = &attr.meta {
        !matches!(expects_path_decoration(&ml.path), Ok(Some(_)))
    } else {
        true
    }
}

fn not_refine_attribute(attr: &syn::Attribute) -> bool {
    if let Meta::List(ml) = &attr.meta {
        !matches!(expects_refine(&ml.path), Ok(Some(_)))
    } else {
        true
    }
}

#[proc_macro_attribute]
pub fn attributes(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item: Item = parse_macro_input!(item);

    struct AttrVisitor;

    use syn::visit_mut;
    impl VisitMut for AttrVisitor {
        fn visit_item_trait_mut(&mut self, item: &mut ItemTrait) {
            for ti in item.items.iter_mut() {
                if let TraitItem::Fn(fun) = ti {
                    fun.attrs.retain(not_hax_attribute)
                }
            }
            visit_mut::visit_item_trait_mut(self, item);
        }
        fn visit_type_mut(&mut self, _type: &mut Type) {}
        fn visit_item_impl_mut(&mut self, item: &mut ItemImpl) {
            for ii in item.items.iter_mut() {
                if let ImplItem::Fn(fun) = ii {
                    fun.attrs.retain(not_hax_attribute)
                }
            }
            visit_mut::visit_item_impl_mut(self, item);
        }
        fn visit_item_mut(&mut self, item: &mut Item) {
            visit_mut::visit_item_mut(self, item);

            match item {
                Item::Struct(s) => {
                    for field in s.fields.iter_mut() {
                        field.attrs.retain(not_refine_attribute)
                    }
                }
                _ => (),
            }
        }
    }

    let mut item = item;
    AttrVisitor.visit_item_mut(&mut item);

    quote! { #item }.into()
}
