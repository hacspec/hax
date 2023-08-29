use crate::prelude::*;

pub type Path = Vec<String>;

pub type Symbol = String;
impl<'t, S> SInto<S, Symbol> for rustc_span::symbol::Symbol {
    fn sinto(&self, _s: &S) -> Symbol {
        self.to_ident_string()
    }
}

pub type Mutability = bool;
impl<S> SInto<S, Mutability> for rustc_hir::Mutability {
    fn sinto(&self, _s: &S) -> Mutability {
        match self {
            rustc_hir::Mutability::Mut => true,
            _ => false,
        }
    }
}
