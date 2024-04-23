use crate::prelude::*;

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

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ItemAttributes {
    attributes: Vec<Attribute>,
    parent_attributes: Vec<Attribute>,
}

impl ItemAttributes {
    pub fn new() -> Self {
        ItemAttributes {
            attributes: vec![],
            parent_attributes: vec![],
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TypedConstantKind {
    pub typ: Ty,
    pub constant_kind: ConstantExpr,
}

lazy_static::lazy_static! {
    pub static ref CORE_EXTRACTION_MODE: bool =
        std::env::var_os("HAX_CORE_EXTRACTION_MODE") == Some("on".into());
}

impl ItemAttributes {
    pub fn from_owner_id<'tcx, S: BaseState<'tcx>>(
        s: &S,
        oid: rustc_hir::hir_id::OwnerId,
    ) -> ItemAttributes {
        if *CORE_EXTRACTION_MODE {
            return ItemAttributes::new();
        }
        use rustc_hir::hir_id::HirId;
        let tcx = s.base().tcx;
        let hir = tcx.hir();
        let attrs_of = |id| tcx.hir().attrs(HirId::from(id)).sinto(s);
        ItemAttributes {
            attributes: attrs_of(oid),
            parent_attributes: hir
                .parent_owner_iter(HirId::from(oid))
                .map(|(oid, _)| oid)
                .map(attrs_of)
                .flatten()
                .collect(),
        }
    }
    pub fn from_def_id<'tcx, S: BaseState<'tcx>>(
        s: &S,
        did: rustc_span::def_id::DefId,
    ) -> ItemAttributes {
        if let Some(def_id) = did.as_local() {
            Self::from_owner_id(s, rustc_hir::hir_id::OwnerId { def_id })
        } else {
            return ItemAttributes::new();
        }
    }
}
