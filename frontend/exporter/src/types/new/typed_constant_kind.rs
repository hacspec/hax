use crate::prelude::*;

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TypedConstantKind {
    pub typ: Ty,
    pub constant_kind: ConstantExpr,
}

#[cfg(feature = "full")]
impl<'tcx, S: BaseState<'tcx> + HasOwnerId> SInto<S, TypedConstantKind>
    for rustc_middle::mir::ConstantKind<'tcx>
{
    fn sinto(&self, s: &S) -> TypedConstantKind {
        TypedConstantKind {
            typ: self.ty().sinto(s),
            constant_kind: self.sinto(s),
        }
    }
}
