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

/// The various strings allowed as decoration kinds.
pub const DECORATION_KINDS: &[&str] = &["decreases", "ensures", "requires"];

/// Expects a `Path` to be a decoration kind: `::hax_lib::<KIND>`,
/// `hax_lib::<KIND>` or `<KIND>` in (with `KIND` in
/// `DECORATION_KINDS`).
pub fn expects_path_decoration(path: &Path) -> Result<Option<String>> {
    let path_span = path.span();
    let path = path
        .expect_simple_path()
        .ok_or_else(|| Error::new(path_span, "Expected a simple path, with no `<...>`."))?;
    Ok(
        match path
            .iter()
            .map(|x| x.as_str())
            .collect::<Vec<_>>()
            .as_slice()
        {
            [kw] | ["", "hax_lib", kw] | ["hax_lib", kw] if DECORATION_KINDS.contains(kw) => {
                Some(kw.to_string())
            }
            _ => None,
        },
    )
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
