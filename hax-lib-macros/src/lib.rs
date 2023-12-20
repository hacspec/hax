mod rewrite_self;
mod syn_ext;
mod utils;

mod prelude {
    pub use proc_macro as pm;
    pub use proc_macro2::*;
    pub use proc_macro_error::*;
    pub use quote::*;
    pub use syn::spanned::Spanned;
    pub use syn::{visit_mut::VisitMut, *};

    pub use hax_lib_macros_types::*;
    pub use AttrPayload::Language as AttrHaxLang;
    pub type FnLike = syn::ImplItemFn;
}

use prelude::*;
use syn_ext::*;
use utils::*;

/// Include this item in the Hax translation.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn include(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: TokenStream = item.into();
    let _ = parse_macro_input!(attr as parse::Nothing);
    let attr = AttrPayload::ItemStatus(ItemStatus::Included { late_skip: false });
    quote! {#attr #item}.into()
}

/// Exclude this item from the Hax translation.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn exclude(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: TokenStream = item.into();
    let _ = parse_macro_input!(attr as parse::Nothing);
    let attr = AttrPayload::ItemStatus(ItemStatus::Excluded { modeled_by: None });
    quote! {#attr #item}.into()
}

/*
TODO: no support in any backends (see #297)

/// Exclude this item from the Hax translation, and replace it with a
/// axiomatized model in each backends. The path of the axiomatized
/// model should be given in Rust syntax.
///
/// # Example
///
/// ```
/// use hax_lib_macros::*;
/// #[modeled_by(FStar::IO::debug_print_string)]
/// fn f(line: String) {
///   println!("{}", line)
/// }
/// ```
#[proc_macro_error]
#[proc_macro_attribute]
pub fn modeled_by(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    use quote::ToTokens;
    let model_path = parse_macro_input!(attr as syn::Path).to_token_stream();
    let item: TokenStream = item.into();
    let attr = AttrPayload::ItemStatus(ItemStatus::Excluded {
        modeled_by: Some(model_path.to_string()),
    });
    quote! {#attr #item}.into()
}
*/

/// Mark a `Proof<{STATEMENT}>`-returning function as a lemma, where
/// `STATEMENT` is a boolean expression capturing any input
/// variable.
/// In the backends, this will generate a lemma with an empty proof.
///
/// # Example
///
/// ```
/// use hax_lib_macros::*;
// #[decreases((m, n))] (TODO: see #297)
/// pub fn ackermann(m: u64, n: u64) -> u64 {
///     match (m, n) {
///         (0, _) => n + 1,
///         (_, 0) => ackermann(m - 1, 1),
///         _ => ackermann(m - 1, ackermann(m, n - 1)),
///     }
/// }
///
/// #[lemma]
/// /// $`\forall n \in \mathbb{N}, \textrm{ackermann}(2, n) = 2 (n + 3) - 3`$
/// pub fn ackermann_property_m1(n: u64) -> Proof<{ ackermann(2, n) == 2 * (n + 3) - 3 }> {}
/// ```
#[proc_macro_error]
#[proc_macro_attribute]
pub fn lemma(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let mut item: syn::ItemFn = parse_macro_input!(item as ItemFn);
    use std::borrow::Borrow;
    use syn::{spanned::Spanned, GenericArgument, PathArguments, ReturnType};

    /// Parses a `syn::Type` of the shape `Proof<{FORMULA}>`.
    fn parse_proof_type(r#type: syn::Type) -> Option<syn::Expr> {
        let syn::Type::Path(syn::TypePath {
            qself: None,
            path:
                syn::Path {
                    leading_colon: None,
                    segments,
                },
        }) = r#type
        else {
            return None;
        };
        let ps = (segments.len() == 1).then_some(()).and(segments.first())?;
        (ps.ident.to_string() == "Proof").then_some(())?;
        let PathArguments::AngleBracketed(args) = &ps.arguments else {
            None?
        };
        let args = args.args.clone();
        let GenericArgument::Const(e) = (args.len() == 1).then_some(()).and(args.first())? else {
            None?
        };
        Some(e.clone())
    }
    let _ = parse_macro_input!(attr as parse::Nothing);
    let attr = &AttrPayload::Lemma;
    if let ReturnType::Type(_, r#type) = &item.sig.output {
        if !match r#type.borrow() {
            syn::Type::Tuple(tt) => tt.elems.is_empty(),
            _ => match parse_proof_type(*r#type.clone()) {
                Some(ensures_clause) => {
                    item.sig.output = ReturnType::Default;
                    return ensures(
                        quote! {|_| #ensures_clause}.into(),
                        quote! { #attr #item }.into(),
                    )
                    .into();
                }
                None => false,
            },
        } {
            abort!(
                item.sig.output.span(),
                "A lemma is expected to return a `Proof<{STATEMENT}>`, where {STATEMENT} is a boolean expression."
            );
        }
    }
    quote! { #attr #item }.into()
}

/*
TODO: this is disabled for now, we need `dyn` types (see issue #296)

/// Provide a measure for a function: this measure will be used once
/// extracted in a backend for checking termination. The expression
/// that decreases can be of any type. (TODO: this is probably as it
/// is true only for F*, see #297)
///
/// # Example
///
/// ```
/// use hax_lib_macros::*;
/// #[decreases((m, n))]
/// pub fn ackermann(m: u64, n: u64) -> u64 {
///     match (m, n) {
///         (0, _) => n + 1,
///         (_, 0) => ackermann(m - 1, 1),
///         _ => ackermann(m - 1, ackermann(m, n - 1)),
///     }
/// }
/// ```
#[proc_macro_error]
#[proc_macro_attribute]
pub fn decreases(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let phi: syn::Expr = parse_macro_input!(attr);
    let item: FnLike = parse_macro_input!(item);
    let (requires, attr) = make_fn_decoration(
        phi,
        item.sig.clone(),
        FnDecorationKind::Decreases,
        None,
        None,
    );
    quote! {#requires #attr #item}.into()
}
*/

/// Add a logical precondition to a function.
// Note you can use the `forall` and `exists` operators. (TODO: commented out for now, see #297)
///
/// # Example
///
/// ```
/// use hax_lib_macros::*;
/// #[requires(x.len() == y.len())]
// #[requires(x.len() == y.len() && forall(|i: usize| i >= x.len() || y[i] > 0))] (TODO: commented out for now, see #297)
/// pub fn div_pairwise(x: Vec<u64>, y: Vec<u64>) -> Vec<u64> {
///     x.iter()
///         .copied()
///         .zip(y.iter().copied())
///         .map(|(x, y)| x / y)
///         .collect()
/// }
/// ```
#[proc_macro_error]
#[proc_macro_attribute]
pub fn requires(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let phi: syn::Expr = parse_macro_input!(attr);
    let item: FnLike = parse_macro_input!(item);
    let (requires, attr) = make_fn_decoration(
        phi.clone(),
        item.sig.clone(),
        FnDecorationKind::Requires,
        None,
        None,
    );
    let mut item_with_debug = item.clone();
    item_with_debug
        .block
        .stmts
        .insert(0, parse_quote! {debug_assert!(#phi);});
    quote! {
        #requires #attr
        // TODO: disable `assert!`s for now (see #297)
        #item
        // #[cfg(    all(not(#HaxCfgOptionName),     debug_assertions )) ] #item_with_debug
        // #[cfg(not(all(not(#HaxCfgOptionName),     debug_assertions )))] #item
    }
    .into()
}

/// Add a logical postcondition to a function. Note you can use the
/// `forall` and `exists` operators.
///
/// # Example
///
/// ```
/// use hax_lib_macros::*;
/// #[ensures(|result| result == x * 2)]
/// pub fn twice(x: u64) -> u64 {
///     x + x
/// }
/// ```
#[proc_macro_error]
#[proc_macro_attribute]
pub fn ensures(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let ExprClosure1 {
        arg: ret_binder,
        body: phi,
    } = parse_macro_input!(attr);
    let item: FnLike = parse_macro_input!(item);
    let kind = FnDecorationKind::Ensures {
        ret_binder: ret_binder.clone(),
    };
    let (ensures, attr) = make_fn_decoration(phi.clone(), item.sig.clone(), kind, None, None);
    let mut item_with_debug = item.clone();
    let body = item.block.clone();
    item_with_debug.block.stmts =
        parse_quote!(let #ret_binder = #body; debug_assert!(#phi); #ret_binder);
    quote! {
        #ensures #attr
        // TODO: disable `assert!`s for now (see #297)
        #item
        // #[cfg(    all(not(#HaxCfgOptionName),     debug_assertions )) ] #item_with_debug
        // #[cfg(not(all(not(#HaxCfgOptionName),     debug_assertions )))] #item
    }
    .into()
}

struct ImplFnDecoration {
    pub kind: FnDecorationKind,
    pub phi: Expr,
    pub generics: Generics,
    pub self_ty: Type,
}

mod kw {
    syn::custom_keyword!(decreases);
    syn::custom_keyword!(ensures);
    syn::custom_keyword!(requires);
    syn::custom_keyword!(refine);
}

impl parse::Parse for ImplFnDecoration {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let parse_next = || -> Result<_> {
            input.parse::<Token![,]>()?;
            let mut generics = input.parse::<Generics>()?;
            input.parse::<Token![,]>()?;
            generics.where_clause = input.parse::<Option<WhereClause>>()?;
            input.parse::<Token![,]>()?;
            let self_ty = input.parse::<Type>()?;
            input.parse::<Token![,]>()?;
            Ok((generics, self_ty))
        };
        let kind = if let Ok(_) = input.parse::<kw::decreases>() {
            FnDecorationKind::Decreases
        } else if let Ok(_) = input.parse::<kw::requires>() {
            FnDecorationKind::Requires
        } else if let Ok(_) = input.parse::<kw::ensures>() {
            let (generics, self_ty) = parse_next()?;
            let ExprClosure1 { arg, body } = input.parse::<ExprClosure1>()?;
            input.parse::<syn::parse::Nothing>()?;
            return Ok(ImplFnDecoration {
                kind: FnDecorationKind::Ensures { ret_binder: arg },
                phi: body,
                generics,
                self_ty,
            });
        } else {
            return Err(input.lookahead1().error());
        };
        let (generics, self_ty) = parse_next()?;
        let phi = input.parse::<Expr>()?;
        input.parse::<syn::parse::Nothing>()?;
        Ok(ImplFnDecoration {
            kind,
            phi,
            generics,
            self_ty,
        })
    }
}

/// Internal macro for dealing with function decorations
/// (`#[decreases(...)]`, `#[ensures(...)]`, `#[requires(...)]`) on
/// `fn` items within an `impl` block. There is special handling since
/// such functions might have a `self` argument: in such cases, we
/// rewrite function decorations as `#[impl_fn_decoration(<KIND>,
/// <GENERICS>, <WHERE CLAUSE>, <SELF TYPE>, <BODY>)]`.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn impl_fn_decoration(attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let ImplFnDecoration {
        kind,
        phi,
        generics,
        self_ty,
    } = parse_macro_input!(attr);
    let mut item: FnLike = parse_macro_input!(item);
    let (decoration, attr) =
        make_fn_decoration(phi, item.sig.clone(), kind, Some(generics), Some(self_ty));
    let decoration = Stmt::Item(Item::Verbatim(decoration));
    item.block.stmts.insert(0, decoration);
    quote! {#attr #item}.into()
}

/// Enable the following attrubutes in the annotated item and sub-items:
/// - (in a struct) `refine`: refine a type with a logical formula
/// - (on a `fn` in an `impl`) `decreases`, `ensures`, `requires`:
///   behave exactly as documented above on the proc attributes of the
///   same name.
///
/// # Example
///
/// ```
/// #[hax_lib_macros::attributes]
/// mod foo {
///     pub struct Hello {
///         pub x: u32,
///         #[refine(y > 3)]
///         pub y: u32,
///         #[refine(y + x + z > 3)]
///         pub z: u32,
///     }
///     impl Hello {
///         fn sum(&self) -> u32 {
///             self.x + self.y + self.z
///         }
///         #[ensures(|result| result - n == self.sum())]
///         fn plus(self, n: u32) -> u32 {
///             self.sum() + n
///         }
///     }
/// }
/// ```
#[proc_macro_error]
#[proc_macro_attribute]
pub fn attributes(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: Item = parse_macro_input!(item);

    struct AttrVisitor {}

    use syn::visit_mut;
    impl VisitMut for AttrVisitor {
        fn visit_item_impl_mut(&mut self, item: &mut ItemImpl) {
            for ii in item.items.iter_mut() {
                if let ImplItem::Fn(fun) = ii {
                    for attr in fun.attrs.iter_mut() {
                        if let Meta::List(ml) = &mut attr.meta {
                            let decoration = &ml.path;
                            if decoration.ends_with("requires")
                                || decoration.ends_with("ensures")
                                || decoration.ends_with("decreases")
                            {
                                let tokens = ml.tokens.clone();
                                let (generics, self_ty) = (&item.generics, &item.self_ty);
                                let where_clause = &generics.where_clause;
                                ml.tokens = quote! {#decoration, #generics, #where_clause, #self_ty, #tokens};
                                ml.path = parse_quote! {::hax_lib_macros::impl_fn_decoration};
                            }
                        }
                    }
                }
            }
            visit_mut::visit_item_impl_mut(self, item);
        }
        fn visit_item_mut(&mut self, item: &mut Item) {
            visit_mut::visit_item_mut(self, item);

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
                                if attr.path().ends_with("refine") {
                                    let payload = attr.parse_args().ok()?;
                                    Some((attr, payload))
                                } else {
                                    None
                                }
                            });
                        if let Some((attr, refine)) = refine {
                            let binders: TokenStream = prev
                                .iter()
                                .map(|(name, ty)| quote! {#name: #ty, })
                                .collect();
                            let uid = ItemUid::fresh();
                            let uid_attr = AttrPayload::Uid(uid.clone());
                            let assoc_attr = AttrPayload::AssociatedItem {
                                role: AssociationRole::Refine,
                                item: uid,
                            };
                            *attr = syn::parse_quote! { #assoc_attr };
                            let status_attr =
                                &AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true });
                            extra.push(syn::parse_quote! {
                                #[cfg(#HaxCfgOptionName)]
                                #status_attr
                                const _: () = {
                                    #uid_attr
                                    #status_attr
                                    fn refinement(#binders) -> bool { #refine }
                                };
                            })
                        }
                    }
                }
                _ => (),
            }
            let extra: TokenStream = extra.iter().map(|extra| quote! {#extra}).collect();
            *item = Item::Verbatim(quote! {#extra #item});
        }
    }

    let mut v = AttrVisitor {};
    let mut item = item;
    v.visit_item_mut(&mut item);

    quote! { #item }.into()
}
