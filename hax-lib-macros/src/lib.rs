mod quote;
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
    use AttrPayload::NeverDropBody;
    quote! { #attr #NeverDropBody #item }.into()
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
                                ml.path = parse_quote! {::hax_lib::impl_fn_decoration};
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

/// Mark a struct or an enum opaque: the extraction will assume the
/// type without revealing its definition.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn opaque_type(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: Item = parse_macro_input!(item);
    let attr = AttrPayload::OpaqueType;
    quote! {#attr #item}.into()
}

/// A marker indicating a `fn` as a ProVerif process read.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn process_read(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: ItemFn = parse_macro_input!(item);
    let attr = AttrPayload::ProcessRead;
    quote! {#attr #item}.into()
}

/// A marker indicating a `fn` as a ProVerif process write.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn process_write(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: ItemFn = parse_macro_input!(item);
    let attr = AttrPayload::ProcessWrite;
    quote! {#attr #item}.into()
}

/// A marker indicating a `fn` as a ProVerif process initialization.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn process_init(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: ItemFn = parse_macro_input!(item);
    let attr = AttrPayload::ProcessInit;
    quote! {#attr #item}.into()
}

/// A marker indicating an `enum` as describing the protocol messages.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn protocol_messages(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: ItemEnum = parse_macro_input!(item);
    let attr = AttrPayload::ProtocolMessages;
    quote! {#attr #item}.into()
}

/// A marker indicating a `fn` should be automatically translated to a ProVerif constructor.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn pv_constructor(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: ItemFn = parse_macro_input!(item);
    let attr = AttrPayload::PVConstructor;
    quote! {#attr #item}.into()
}

/// A marker indicating a `fn` requires manual modelling in ProVerif.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn pv_handwritten(_attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let item: ItemFn = parse_macro_input!(item);
    let attr = AttrPayload::PVHandwritten;
    quote! {#attr #item}.into()
}

/// Create a mathematical integer. This macro expects a integer
/// literal that consists in an optional minus sign followed by one or
/// more digits.
#[proc_macro_error]
#[proc_macro]
pub fn int(payload: pm::TokenStream) -> pm::TokenStream {
    let mut tokens = payload.into_iter().peekable();
    let negative = matches!(tokens.peek(), Some(pm::TokenTree::Punct(p)) if p.as_char() == '-');
    if negative {
        tokens.next();
    }
    let [pm::TokenTree::Literal(lit)] = &tokens.collect::<Vec<_>>()[..] else {
        abort_call_site!("Expected exactly one numeric literal");
    };
    let lit = format!("{lit}");
    // Allow negative numbers
    let mut lit = lit.strip_prefix("-").unwrap_or(lit.as_str()).to_string();
    if let Some(faulty) = lit.chars().find(|ch| !matches!(ch, '0'..='9')) {
        abort_call_site!(format!("Expected a digit, found {faulty}"));
    }
    if negative {
        lit = format!("-{lit}");
    }
    quote! {
        ::hax_lib::int::Int::_unsafe_from_str(#lit)
    }
    .into()
}

macro_rules! make_quoting_item_proc_macro {
    ($backend:ident, $macro_name:ident, $position:expr, $cfg_name:ident) => {
        #[doc = concat!("This macro inlines verbatim ", stringify!($backend)," code before a Rust item.")]
        ///
        /// This macro takes a string literal containing backend
        /// code. Just as backend expression macros, this literal can
        /// contains dollar-prefixed Rust names.
        ///
        /// Note: when targetting F*, you can prepend a first
        /// comma-separated argument: `interface`, `impl` or
        /// `both`. This controls where the code will apprear: in the
        /// `fst` or `fsti` files or both.
        #[proc_macro_error]
        #[proc_macro_attribute]
        pub fn $macro_name(payload: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
            let mut fstar_options = None;
            let item: TokenStream = item.into();
            let payload = {
                let mut tokens = payload.into_iter().peekable();
                if let Some(pm::TokenTree::Ident(ident)) = tokens.peek() {
                    let ident_str = format!("{}", ident);
                    fstar_options = Some(ItemQuoteFStarOpts {
                        intf: ident_str == "interface" || ident_str == "both",
                        r#impl: ident_str == "impl" || ident_str == "both",
                    });
                    if !matches!(ident_str.as_str(), "impl" | "both" | "interface") {
                        proc_macro_error::abort!(
                            ident.span(),
                            "Expected `impl`, `both` or `interface`"
                        );
                    }
                    // Consume the ident
                    let _ = tokens.next();
                    // Expect a comma, fail otherwise
                    let comma = pm::TokenStream::from_iter(tokens.next().into_iter());
                    let _: syn::token::Comma = parse_macro_input!(comma);
                }
                pm::TokenStream::from_iter(tokens)
            };

            let ts: TokenStream = quote::item(
                ItemQuote {
                    position: $position,
                    fstar_options,
                },
                quote! {#[cfg($cfg_name)]},
                payload,
                quote! {#item}.into(),
            )
            .into();
            ts.into()
        }
    };
}

macro_rules! make_quoting_proc_macro {
    ($backend:ident($expr_name:ident, $before_name:ident, $after_name:ident, $replace_name:ident, $cfg_name:ident)) => {
        #[doc = concat!("Embed ", stringify!($backend), " expression inside a Rust expression. This macro takes only one argument: some raw ", stringify!($backend), " code as a string literal.")]
        ///

        /// While it is possible to directly write raw backend code,
        /// sometimes it can be inconvenient. For example, referencing
        /// Rust names can be a bit cumbersome: for example, the name
        /// `my_crate::my_module::CONSTANT` might be translated
        /// differently in a backend (e.g. in the F* backend, it will
        /// probably be `My_crate.My_module.v_CONSTANT`).
        ///

        /// To facilitate this, you can write Rust names directly,
        /// using the prefix `$`: `f $my_crate::my_module__CONSTANT + 3`
        /// will be replaced with `f My_crate.My_module.v_CONSTANT + 3`
        /// in the F* backend for instance.

        /// If you want to refer to the Rust constructor
        /// `Enum::Variant`, you should write `$$Enum::Variant` (note
        /// the double dollar).

        /// If the name refers to something polymorphic, you need to
        /// signal it by adding _any_ type informations,
        /// e.g. `${my_module::function<()>}`. The curly braces are
        /// needed for such more complex expressions.

        /// You can also write Rust patterns with the `$?{SYNTAX}`
        /// syntax, where `SYNTAX` is a Rust pattern. The syntax
        /// `${EXPR}` also allows any Rust expressions
        /// `EXPR` to be embedded.

        /// Types can be refered to with the syntax `$:{TYPE}`.
        #[proc_macro]
        pub fn $expr_name(payload: pm::TokenStream) -> pm::TokenStream {
            let ts: TokenStream = quote::expression(payload).into();
            quote!{
                #[cfg($cfg_name)]
                {
                    #ts
                }
            }.into()
        }

        make_quoting_item_proc_macro!($backend, $before_name, ItemQuotePosition::Before, $cfg_name);
        make_quoting_item_proc_macro!($backend, $after_name, ItemQuotePosition::After, $cfg_name);

        #[doc = concat!("Replaces a Rust expression with some verbatim ", stringify!($backend)," code.")]
        #[proc_macro_error]
        #[proc_macro_attribute]
        pub fn $replace_name(payload: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
            let item: TokenStream = item.into();
            let attr = AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true });
            $before_name(payload, quote!{#attr #item}.into())
        }
    };
    ($backend:ident $payload:tt $($others:tt)+) => {
        make_quoting_proc_macro!($backend$payload);
        make_quoting_proc_macro!($($others)+);
    }
}

make_quoting_proc_macro!(fstar(fstar_expr, fstar_before, fstar_after, fstar_replace, hax_backend_fstar)
                         coq(coq_expr, coq_before, coq_after, coq_replace, hax_backend_coq)
                         proverif(proverif_expr, proverif_before, proverif_after, proverif_replace, hax_backend_proverif));

/// Marks a newtype `struct RefinedT(T);` as a refinement type. The
/// struct should have exactly one unnamed private field.
///
/// This macro takes one argument: a boolean predicate that refines
/// values of type `SomeType`.
///
/// For example, the following type defines bounded `u64` integers.
///
/// ```
/// #[hax_lib::refinement_type(|x| x >= MIN && x <= MAX)]
/// pub struct BoundedU64<const MIN: u64, const MAX: u64>(u64);
/// ```
///
/// This macro will generate an implementation of the [`Deref`] trait
/// and of the [`hax_lib::Refinement`] type. Those two traits are
/// the only interface to this newtype: one is allowed only to
/// construct or destruct refined type via those smart constructors
/// and destructors, ensuring the abstraction.
///
/// A refinement of a type `T` with a formula `f` can be seen as a box
/// that contains a value of type `T` and a proof that this value
/// satisfies the formula `f`.
///
/// In debug mode, the refinement will be checked at run-time. This
/// requires the base type `T` to implement `Clone`. Pass a first
/// parameter `no_debug_runtime_check` to disable this behavior.
///
/// When extracted via hax, this is interpreted in the backend as a
/// refinement type: the use of such a type yields static proof
/// obligations.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn refinement_type(mut attr: pm::TokenStream, item: pm::TokenStream) -> pm::TokenStream {
    let mut item = parse_macro_input!(item as syn::ItemStruct);

    let syn::Fields::Unnamed(fields) = &item.fields else {
        proc_macro_error::abort!(
            item.generics.span(),
            "Expected a newtype (a struct with one unnamed field), got one or more named field"
        );
    };
    let paren_token = fields.paren_token;
    let fields = fields.unnamed.iter().collect::<Vec<_>>();
    let [field] = &fields[..] else {
        proc_macro_error::abort!(
            item.generics.span(),
            "Expected a newtype (a struct with one unnamed field), got {} fields",
            fields.len()
        );
    };
    if field.vis != syn::Visibility::Inherited {
        proc_macro_error::abort!(field.vis.span(), "This field was expected to be private");
    }

    let no_debug_assert = {
        let mut tokens = attr.clone().into_iter();
        if let (Some(pm::TokenTree::Ident(ident)), Some(pm::TokenTree::Punct(comma))) =
            (tokens.next(), tokens.next())
        {
            if ident.to_string() != "no_debug_runtime_check" {
                proc_macro_error::abort!(ident.span(), "Expected 'no_debug_runtime_check'");
            }
            if comma.as_char() != ',' {
                proc_macro_error::abort!(ident.span(), "Expected a comma");
            }
            attr = pm::TokenStream::from_iter(tokens);
            true
        } else {
            false
        }
    };

    let ExprClosure1 {
        arg: ret_binder,
        body: phi,
    } = parse_macro_input!(attr);

    let kind = FnDecorationKind::Ensures {
        ret_binder: ret_binder.clone(),
    };
    let sig = syn::Signature {
        constness: None,
        asyncness: None,
        unsafety: None,
        abi: None,
        variadic: None,
        fn_token: syn::Token![fn](item.span()),
        ident: parse_quote! {dummy},
        generics: item.generics.clone(),
        paren_token,
        inputs: syn::punctuated::Punctuated::new(),
        output: syn::ReturnType::Type(parse_quote! {->}, Box::new(field.ty.clone())),
    };
    let ident = &item.ident;
    let generics = &item.generics;
    let vis = item.vis.clone();
    let generics_args: syn::punctuated::Punctuated<_, syn::token::Comma> = item
        .generics
        .params
        .iter()
        .map(|g| match g {
            syn::GenericParam::Lifetime(p) => {
                let i = &p.lifetime;
                quote! { #i }
            }
            syn::GenericParam::Type(p) => {
                let i = &p.ident;
                quote! { #i }
            }
            syn::GenericParam::Const(p) => {
                let i = &p.ident;
                quote! { #i }
            }
        })
        .collect();
    let inner_ty = &field.ty;
    let (refinement_item, refinement_attr) = make_fn_decoration(phi.clone(), sig, kind, None, None);
    let module_ident = syn::Ident::new(
        &format!("hax__autogenerated_refinement__{}", ident),
        ident.span(),
    );

    item.vis = parse_quote! {pub};
    let debug_assert =
        no_debug_assert.then_some(quote! {::core::debug_assert!(Self::invariant(x.clone()));});
    let newtype_as_ref_attr = AttrPayload::NewtypeAsRefinement;
    quote! {
        #[allow(non_snake_case)]
        mod #module_ident {
            #[allow(unused_imports)]
            use super::*;

            #refinement_item

            #newtype_as_ref_attr
            #refinement_attr
            #item

            #[::hax_lib::exclude]
            impl #generics ::hax_lib::Refinement for #ident <#generics_args> {

                type InnerType = #inner_ty;

                fn new(x: Self::InnerType) -> Self {
                    #debug_assert
                    Self(x)
                }
                fn get(self) -> Self::InnerType {
                    self.0
                }
                fn get_mut(&mut self) -> &mut Self::InnerType {
                    &mut self.0
                }
                fn invariant(#ret_binder: Self::InnerType) -> bool {
                    #phi
                }
            }

            #[::hax_lib::exclude]
            impl #generics ::std::ops::Deref for #ident <#generics_args> {
                type Target = #inner_ty;
                fn deref(&self) -> &Self::Target {
                    &self.0
                }
            }

            #[::hax_lib::exclude]
            impl #generics ::hax_lib::RefineAs<#ident <#generics_args>> for #inner_ty {
                fn into_checked(self) -> #ident <#generics_args> {
                    use ::hax_lib::Refinement;
                    #ident::new(self)
                }
            }
        }
        #vis use #module_ident::#ident;

    }
    .into()
}
