use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct TypedConstantKind {
    pub typ: Ty,
    pub constant_kind: ConstantExpr,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: BaseState<'tcx> + HasOwnerId> SInto<S, TypedConstantKind>
    for rustc_middle::mir::Const<'tcx>
{
    fn sinto(&self, s: &S) -> TypedConstantKind {
        TypedConstantKind {
            typ: self.ty().sinto(s),
            constant_kind: self.sinto(s),
        }
    }
}
