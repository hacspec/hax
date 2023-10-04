use crate::prelude::*;

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

lazy_static::lazy_static! {
    pub static ref CORE_EXTRACTION_MODE: bool =
        std::env::var_os("HAX_CORE_EXTRACTION_MODE") == Some("on".into());
}

impl ItemAttributes {
    pub fn from_owner_id<'tcx, S: UnderOwnerState<'tcx>>(
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
}
