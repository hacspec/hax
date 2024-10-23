use crate::syn_ext::*;
use proc_macro2::Span;
use syn::spanned::Spanned;
use syn::*;

/// The `RewriteSelf` structure is hidden in a module so that only its
/// method can mutate its fields.
mod rewrite_self {
    use super::*;
    use std::collections::HashSet;

    /// Small & dirty wrapper around spans to make them `Eq`,
    /// `PartialEq` and `Hash`
    #[derive(Clone, Debug)]
    struct SpanWrapper(Span);
    const _: () = {
        impl Eq for SpanWrapper {}
        impl PartialEq for SpanWrapper {
            fn eq(&self, other: &Self) -> bool {
                format!("{self:?}") == format!("{other:?}")
            }
        }
        use std::hash::*;
        impl Hash for SpanWrapper {
            fn hash<H: Hasher>(&self, state: &mut H) {
                format!("{self:?}").hash(state)
            }
        }
    };

    /// A struct that carries informations for substituting `self` and
    /// `Self`. Note `typ` is an option:
    #[must_use]
    pub struct RewriteSelf {
        typ: Option<Type>,
        ident: Ident,
        self_spans: HashSet<SpanWrapper>,
    }

    impl RewriteSelf {
        /// Consumes `RewriteSelf`, optionally outputing errors.
        pub fn get_error(self) -> Option<proc_macro2::TokenStream> {
            if self.typ.is_some() || self.self_spans.is_empty() {
                return None;
            }

            let mut error = Error::new(Span::call_site(), "This macro doesn't work on trait or impl items: you need to add a `#[hax_lib::attributes]` on the enclosing impl block or trait.");
            for SpanWrapper(span) in self.self_spans {
                let use_site = Error::new(
                    span,
                    "Here, the function you are trying to annotate has a `Self`.",
                );
                error.combine(use_site);
            }
            Some(error.to_compile_error())
        }

        fn self_detected(&mut self, span: Span) {
            self.self_spans.insert(SpanWrapper(span));
        }

        /// Requests the ident with which `self` should be substituted.
        pub fn self_ident(&mut self, span: Span) -> &Ident {
            self.self_detected(span);
            &self.ident
        }
        /// Requests the type with which `Self` should be substituted with.
        pub fn self_ty(&mut self, span: Span) -> Type {
            self.self_detected(span);
            self.typ.clone().unwrap_or_else(|| {
                parse_quote! {Self}
            })
        }
        /// Construct a rewritter
        pub fn new(ident: Ident, typ: Option<Type>) -> Self {
            Self {
                typ,
                ident,
                self_spans: HashSet::new(),
            }
        }
    }
}
pub use rewrite_self::*;

impl visit_mut::VisitMut for RewriteSelf {
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        visit_mut::visit_expr_mut(self, e);
        if e.is_ident("self") {
            let into = self.self_ident(e.span()).clone();
            *e = parse_quote! {#into}
        }
    }
    fn visit_type_mut(&mut self, ty: &mut Type) {
        visit_mut::visit_type_mut(self, ty);
        if ty.is_ident("Self") {
            *ty = self.self_ty(ty.span())
        }
    }
    fn visit_fn_arg_mut(&mut self, arg: &mut FnArg) {
        visit_mut::visit_fn_arg_mut(self, arg);
        if let FnArg::Receiver(r) = arg {
            let span = r.self_token.span();
            *arg = FnArg::Typed(PatType {
                attrs: r.attrs.clone(),
                pat: Box::new(Pat::Ident(PatIdent {
                    attrs: vec![],
                    by_ref: None,
                    mutability: None,
                    ident: self.self_ident(span).clone(),
                    subpat: None,
                })),
                colon_token: token::Colon(arg.span()),
                ty: Box::new(self.self_ty(span)),
            });
        }
    }
    fn visit_item_impl_mut(&mut self, _i: &mut ItemImpl) {
        // Do nothing! We allow user to write self if it's nested in a impl block
    }
}
