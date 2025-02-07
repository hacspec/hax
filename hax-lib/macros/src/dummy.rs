mod hax_paths;

use hax_paths::*;
use proc_macro as pm;
use proc_macro2::*;
use proc_macro_error::*;
use quote::*;
use syn::{visit_mut::VisitMut, spanned::Spanned, *};

macro_rules! identity_proc_macro_attribute {
    ($($name:ident,)*) => {
        $(
            #[proc_macro_attribute]
            pub fn $name(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
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
    pv_handwritten,
    pv_constructor,
    protocol_messages,
    process_init,
    process_write,
    process_read,
    opaque,
    opaque_type,
    transparent,
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
    decreases,
);


#[proc_macro_error]
#[proc_macro_attribute]
pub fn requires(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: TokenStream = item.into();
    let payload = format!(r#"Pre-Condition: 
```
{} 
```"#, attr.clone().to_string());
    let phi: syn::Expr = parse_macro_input!(attr);
    let payload = LitStr::new(&payload, phi.span());
    quote! {
        #[doc=#payload]
        #item
    }
    .into()
}


#[proc_macro_error]
#[proc_macro_attribute]
pub fn ensures(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: TokenStream = item.into();
    let payload = format!(r#"Post-Condition: 
``` 
{} 
```"#, attr.clone().to_string());
    let phi: syn::Expr = parse_macro_input!(attr);
    let payload = LitStr::new(&payload, phi.span());
    quote! {
        #[doc=#payload]
        #item
    }
    .into()
}

#[proc_macro]
pub fn fstar_expr(_payload: pm::TokenStream) -> pm::TokenStream {
    quote! { () }.into()
}
#[proc_macro]
pub fn coq_expr(_payload: pm::TokenStream) -> pm::TokenStream {
    quote! { () }.into()
}
#[proc_macro]
pub fn proverif_expr(_payload: pm::TokenStream) -> pm::TokenStream {
    quote! { () }.into()
}

#[proc_macro_attribute]
pub fn lemma(_attr: pm::TokenStream, _item: pm::TokenStream) -> pm::TokenStream {
    quote! {}.into()
}

fn unsafe_expr() -> pm::TokenStream {
    // `*_unsafe_expr("<code>")` are macro generating a Rust expression of any type, that will be replaced by `<code>` in the backends.
    // This should be used solely in hax-only contextes.
    // If this macro is used, that means the user broke this rule.
    quote! { ::std::compile_error!("`hax_lib::unsafe_expr` has no meaning outside of hax extraction, please use it solely on hax-only places.") }.into()
}

#[proc_macro]
pub fn fstar_unsafe_expr(_payload: pm::TokenStream) -> pm::TokenStream {
    unsafe_expr()
}
#[proc_macro]
pub fn coq_unsafe_expr(_payload: pm::TokenStream) -> pm::TokenStream {
    unsafe_expr()
}
#[proc_macro]
pub fn proverif_unsafe_expr(_payload: pm::TokenStream) -> pm::TokenStream {
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
pub fn attributes(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
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

#[proc_macro]
pub fn int(payload: pm::TokenStream) -> pm::TokenStream {
    let mut tokens = payload.into_iter().peekable();
    let negative = matches!(tokens.peek(), Some(pm::TokenTree::Punct(p)) if p.as_char() == '-');
    if negative {
        tokens.next();
    }
    let [lit @ pm::TokenTree::Literal(_)] = &tokens.collect::<Vec<_>>()[..] else {
        return quote! { ::std::compile_error!("Expected exactly one numeric literal") }.into();
    };
    let lit: proc_macro2::TokenStream = pm::TokenStream::from(lit.clone()).into();
    quote! {::hax_lib::int::Int(#lit)}.into()
}

#[proc_macro_attribute]
pub fn impl_fn_decoration(_attr: pm::TokenStream, _item: pm::TokenStream) -> pm::TokenStream {
    quote! { ::std::compile_error!("`impl_fn_decoration` is an internal macro and should never be used directly.") }.into()
}

#[proc_macro_attribute]
pub fn trait_fn_decoration(_attr: pm::TokenStream, _item: pm::TokenStream) -> pm::TokenStream {
    quote! { ::std::compile_error!("`trait_fn_decoration` is an internal macro and should never be used directly.") }.into()
}

#[proc_macro]
pub fn loop_invariant(_predicate: pm::TokenStream) -> pm::TokenStream {
    quote! {}.into()
}
