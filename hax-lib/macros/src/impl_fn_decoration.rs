//! This module defines the `ImplFnDecoration` structure and utils
//! around it.

use crate::prelude::*;
use crate::utils::*;

/// Supporting structure that holds the data required by the internal
/// macro `impl_fn_decoration`.
pub struct ImplFnDecoration {
    pub kind: FnDecorationKind,
    pub phi: Expr,
    pub generics: Generics,
    pub self_ty: Type,
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

        let path = input.parse::<Path>()?;
        let path_span = path.span();
        let kind = match expects_path_decoration(&path)? {
            Some(s) => match s.as_str() {
                "decreases" => FnDecorationKind::Decreases,
                "requires" => FnDecorationKind::Requires,
                "ensures" => {
                    let (generics, self_ty) = parse_next()?;
                    let ExprClosure1 { arg, body } = input.parse::<ExprClosure1>()?;
                    input.parse::<syn::parse::Nothing>()?;
                    return Ok(ImplFnDecoration {
                        kind: FnDecorationKind::Ensures { ret_binder: arg },
                        phi: body,
                        generics,
                        self_ty,
                    });
                }
                _ => unreachable!(),
            }
            None => Err(Error::new(path_span, "Expected `::hax_lib::<KIND>`, `hax_lib::<KIND>` or `<KIND>` with `KIND` in {DECORATION_KINDS:?}"))?,
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
