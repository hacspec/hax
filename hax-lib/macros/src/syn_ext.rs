use crate::prelude::*;
use syn::parse::*;
use syn::punctuated::Punctuated;

/// A closure expression of arity 1, e.g. `|x| x + 3`
pub struct ExprClosure1 {
    pub arg: Pat,
    pub body: Expr,
}

impl Parse for ExprClosure1 {
    fn parse(ps: ParseStream) -> Result<Self> {
        let closure: ExprClosure = Parse::parse(ps as ParseStream)?;
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

/// Utility trait to extract an `Ident` from various syn types
pub trait ExpectIdent {
    /// Is `self` an `Ident`?
    fn expect_ident(&self) -> Option<Ident>;
    /// Is `self` a specific ident named `name`?
    fn is_ident(&self, name: &str) -> bool {
        self.expect_ident()
            .filter(|ident| &ident.to_string() == name)
            .is_some()
    }
}

impl<T: ExpectIdent> ExpectIdent for Box<T> {
    fn expect_ident(&self) -> Option<Ident> {
        let this: &T = self;
        this.expect_ident()
    }
}

fn expect_punctuated_1<T: Clone, S>(x: &Punctuated<T, S>) -> Option<T> {
    (x.len() == 1).then(|| x.first().unwrap().clone())
}

impl ExpectIdent for Path {
    fn expect_ident(&self) -> Option<Ident> {
        expect_punctuated_1(&self.segments).map(|s| s.ident)
    }
}

impl ExpectIdent for Expr {
    fn expect_ident(&self) -> Option<Ident> {
        match self {
            Expr::Path(ExprPath {
                qself: None, path, ..
            }) => path.expect_ident(),
            _ => None,
        }
    }
}

impl ExpectIdent for Type {
    fn expect_ident(&self) -> Option<Ident> {
        match self {
            Type::Path(TypePath {
                qself: None, path, ..
            }) => path.expect_ident(),
            _ => None,
        }
    }
}

impl ExpectIdent for Pat {
    fn expect_ident(&self) -> Option<Ident> {
        match self {
            Pat::Ident(PatIdent {
                by_ref: None,
                mutability: None,
                ident,
                subpat: None,
                ..
            }) => Some(ident.clone()),
            _ => None,
        }
    }
}
