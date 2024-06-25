use crate::prelude::*;
use syn::parse::*;

/// A closure expression of arity 1, e.g. `|x| x + 3`
pub struct ExprClosure1 {
    pub arg: syn::Pat,
    pub body: syn::Expr,
}

// pub trait PatExt {
//     // Make sure to remove type ascriptions
//     fn untype(mut pat: syn::Pat) -> syn::Pat {
//         if let syn::Pat::Type(sub) = pat {
//             pat = *sub.pat.clone();
//         }
//         pat
//     }
// }

impl Parse for ExprClosure1 {
    fn parse(ps: ParseStream) -> Result<Self> {
        let closure: syn::ExprClosure = Parse::parse(ps as ParseStream)?;
        let inputs = closure.inputs;
        if inputs.len() != 1 {
            Err(Error::new(inputs.span(), "Expected exactly one argument"))?;
        }
        Ok(ExprClosure1 {
            arg: inputs[0].clone(),
            body: *closure.body.clone(),
        })
    }
}

pub trait PathExt {
    /// Checks whether a `syn::Path` ends with a certain ident. This
    /// is a bit bad: we have no way of differentiating an Hax
    /// attribute from an attribute from another crate that share a
    /// common name.
    fn ends_with(&self, i: &str) -> bool;
}

impl PathExt for Path {
    fn ends_with(&self, i: &str) -> bool {
        matches!(self.segments.iter().last(), Some(syn::PathSegment {
            ident,
            arguments: syn::PathArguments::None,
        }) if i == ident.to_string().as_str())
    }
}
