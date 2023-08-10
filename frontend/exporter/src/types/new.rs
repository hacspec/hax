use crate::prelude::*;

// impl<'tcx, S: BaseState<'tcx> + HasThir<'tcx>, O: IsOptions> SInto<S, TypedConstantKind<O>>
//     for rustc_middle::mir::ConstantKind<'tcx>
// {
//     fn sinto(&self, s: &S) -> TypedConstantKind<O> {
//         TypedConstantKind {
//             typ: self.ty().sinto(s),
//             constant_kind: self.sinto(s),
//         }
//     }
// }
// #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
// pub struct TypedConstantKind<O: IsOptions> {
//     typ: Ty<O>,
//     constant_kind: ConstantKind<O>,
// }
