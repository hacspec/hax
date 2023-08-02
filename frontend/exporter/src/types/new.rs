use crate::prelude::*;

impl<'tcx, S: BaseState<'tcx> + HasThir<'tcx>> SInto<S, TypedConstantKind>
    for rustc_middle::mir::ConstantKind<'tcx>
{
    fn sinto(&self, s: &S) -> TypedConstantKind {
        TypedConstantKind {
            typ: self.ty().sinto(s),
            constant_kind: self.sinto(s),
        }
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TypedConstantKind {
    typ: Ty,
    constant_kind: ConstantKind,
}
