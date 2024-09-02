pub type Path = Vec<String>;
pub type Mutability = bool;

#[cfg(feature = "rustc")]
mod rustc {
    use super::*;
    use crate::prelude::*;

    impl<'t, S> SInto<S, Symbol> for rustc_span::symbol::Symbol {
        fn sinto(&self, _s: &S) -> Symbol {
            self.to_ident_string()
        }
    }

    impl<S> SInto<S, Mutability> for rustc_hir::Mutability {
        fn sinto(&self, _s: &S) -> Mutability {
            match self {
                rustc_hir::Mutability::Mut => true,
                _ => false,
            }
        }
    }
}
