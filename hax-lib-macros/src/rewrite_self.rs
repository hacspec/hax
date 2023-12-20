use proc_macro2::Span;
use syn::spanned::Spanned;
use syn::*;

mod rewrite_self {
    use super::*;
    pub struct RewriteSelf {
        self_detected: bool,
        typ: Option<Type>,
        ident: Ident,
    }
    impl RewriteSelf {
        pub fn self_ident(&mut self) -> Ident {
            self.self_detected = true;
            self.ident.clone()
        }
        pub fn self_ty(&mut self, span: Span) -> Type {
            self.self_detected = true;
            self.typ.clone().unwrap_or_else(|| {
                Type::Verbatim(Error::new(span, "Detected a `self`").to_compile_error())
            })
        }
        pub fn new(ident: Ident, typ: Option<Type>) -> Self {
            Self {
                typ,
                ident,
                self_detected: false,
            }
        }
    }
}
pub use rewrite_self::*;

impl visit_mut::VisitMut for RewriteSelf {
    fn visit_expr_path_mut(&mut self, i: &mut ExprPath) {
        let ExprPath {
            qself: None,
            path:
                Path {
                    leading_colon: None,
                    segments,
                },
            ..
        } = i
        else {
            return ();
        };
        if segments.len() != 1 {
            return ();
        }
        let Some(PathSegment {
            ident,
            arguments: PathArguments::None,
        }) = segments.first_mut()
        else {
            return ();
        };
        if ident.to_string() == "self" {
            let into = self.self_ident().clone();
            *ident = parse_quote! {#into}
        }
    }
    fn visit_fn_arg_mut(&mut self, arg: &mut FnArg) {
        if let FnArg::Receiver(r) = arg {
            *arg = FnArg::Typed(PatType {
                attrs: r.attrs.clone(),
                pat: Box::new(Pat::Ident(PatIdent {
                    attrs: vec![],
                    by_ref: None,
                    mutability: None,
                    ident: self.self_ident().clone(),
                    subpat: None,
                })),
                colon_token: token::Colon(arg.span()),
                ty: Box::new(self.self_ty(arg.span())),
            });
        }
    }
    fn visit_item_impl_mut(&mut self, _i: &mut ItemImpl) {
        // Do nothing! We allow user to write self if it's nested in a impl block
        ()
    }
}
