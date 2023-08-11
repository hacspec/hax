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

pub type Const = ConstantExpr;

impl<'tcx, S: BaseState<'tcx>> SInto<S, Const> for rustc_middle::ty::Const<'tcx> {
    fn sinto(&self, s: &S) -> Const {
        // SH: TODO: are you sure you want to evaluate the constant straight away?
        // I put some code for the [Unevaluated] case in [const_to_constant_expr]
        let x = self.eval(s.base().tcx, get_param_env(s));
        const_to_constant_expr(s, x)
    }
}
