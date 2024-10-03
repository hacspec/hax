use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ItemAttributes {
    attributes: Vec<Attribute>,
    parent_attributes: Vec<Attribute>,
}

impl Default for ItemAttributes {
    fn default() -> Self {
        Self::new()
    }
}

impl ItemAttributes {
    pub fn new() -> Self {
        ItemAttributes {
            attributes: vec![],
            parent_attributes: vec![],
        }
    }
}

#[cfg(feature = "rustc")]
lazy_static::lazy_static! {
    pub static ref CORE_EXTRACTION_MODE: bool =
        std::env::var_os("HAX_CORE_EXTRACTION_MODE") == Some("on".into());
}

#[cfg(feature = "rustc")]
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
                .flat_map(attrs_of)
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
            ItemAttributes::new()
        }
    }
}
