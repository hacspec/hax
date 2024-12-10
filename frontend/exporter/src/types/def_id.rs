//! This module contains the type definition for `DefId` and the types
//! `DefId` depends on.
//!
//! This is purposely a very small isolated module:
//! `hax-engine-names-extract` uses those types, but we don't want
//! `hax-engine-names-extract` to have a build dependency on the whole
//! frontend, that double the build times for the Rust part of hax.
//!
//! The feature `extract_names_mode` exists only in the crate
//! `hax-engine-names-extract`, and is used to turn off the derive
//! attributes `AdtInto` and `JsonSchema`.

use hax_adt_into::derive_group;

#[cfg(all(not(feature = "extract_names_mode"), feature = "rustc"))]
use crate::prelude::*;
#[cfg(not(feature = "extract_names_mode"))]
use crate::{AdtInto, JsonSchema};

#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;

pub type Symbol = String;

#[cfg(all(not(feature = "extract_names_mode"), feature = "rustc"))]
impl<'t, S> SInto<S, Symbol> for rustc_span::symbol::Symbol {
    fn sinto(&self, _s: &S) -> Symbol {
        self.to_ident_string()
    }
}

/// Reflects [`rustc_hir::def_id::DefId`]
#[derive_group(Serializers)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(JsonSchema))]
pub struct DefId {
    pub(crate) contents: crate::id_table::Node<DefIdContents>,
}

#[derive_group(Serializers)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(JsonSchema))]
pub struct DefIdContents {
    pub krate: String,
    pub path: Vec<DisambiguatedDefPathItem>,
    pub parent: Option<DefId>,
    /// Rustc's `CrateNum` and `DefIndex` raw indexes. This can be
    /// useful if one needs to convert a [`DefId`] into a
    /// [`rustc_hir::def_id::DefId`]; there is a `From` instance for
    /// that purpose.
    ///
    /// **Warning: this `index` field might not be safe to use**. They are
    /// valid only for one Rustc sesssion. Please do not rely on those
    /// indexes unless you cannot do otherwise.
    pub index: (u32, u32),
    pub is_local: bool,

    /// The kind of definition this `DefId` points to.
    #[cfg(not(feature = "extract_names_mode"))]
    pub kind: crate::DefKind,
}

#[cfg(feature = "rustc")]
impl DefId {
    pub fn to_rust_def_id(&self) -> RDefId {
        let (krate, index) = self.index;
        RDefId {
            krate: rustc_hir::def_id::CrateNum::from_u32(krate),
            index: rustc_hir::def_id::DefIndex::from_u32(index),
        }
    }

    /// Iterate over this element and its parents.
    pub fn ancestry(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(Some(self), |def| def.parent.as_ref())
    }

    /// The `PathItem` corresponding to this item.
    pub fn path_item(&self) -> DisambiguatedDefPathItem {
        self.path
            .last()
            .cloned()
            .unwrap_or_else(|| DisambiguatedDefPathItem {
                disambiguator: 0,
                data: DefPathItem::CrateRoot {
                    name: self.krate.clone(),
                },
            })
    }
}

impl std::ops::Deref for DefId {
    type Target = DefIdContents;
    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

#[cfg(not(feature = "rustc"))]
impl std::fmt::Debug for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefId")
            .field("krate", &self.krate)
            .field("path", &self.path)
            .finish()
    }
}

#[cfg(feature = "rustc")]
impl std::fmt::Debug for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use the more legible rustc debug implementation.
        write!(f, "{:?}", rustc_span::def_id::DefId::from(self))
    }
}

impl std::hash::Hash for DefId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // A `DefId` is basically an interned path; we only hash the path, discarding the rest of
        // the information.
        self.krate.hash(state);
        self.path.hash(state);
    }
}

#[cfg(feature = "rustc")]
pub(crate) fn translate_def_id<'tcx, S: BaseState<'tcx>>(s: &S, def_id: RDefId) -> DefId {
    let tcx = s.base().tcx;
    let path = {
        // Set the def_id so the `CrateRoot` path item can fetch the crate name.
        let state_with_id = with_owner_id(s.base(), (), (), def_id);
        tcx.def_path(def_id)
            .data
            .iter()
            .map(|x| x.sinto(&state_with_id))
            .collect()
    };
    let contents = DefIdContents {
        path,
        krate: tcx.crate_name(def_id.krate).to_string(),
        parent: tcx.opt_parent(def_id).sinto(s),
        index: (
            rustc_hir::def_id::CrateNum::as_u32(def_id.krate),
            rustc_hir::def_id::DefIndex::as_u32(def_id.index),
        ),
        is_local: def_id.is_local(),
        #[cfg(not(feature = "extract_names_mode"))]
        kind: tcx.def_kind(def_id).sinto(s),
    };
    let contents =
        s.with_global_cache(|cache| id_table::Node::new(contents, &mut cache.id_table_session));
    DefId { contents }
}

#[cfg(all(not(feature = "extract_names_mode"), feature = "rustc"))]
impl<'s, S: BaseState<'s>> SInto<S, DefId> for RDefId {
    fn sinto(&self, s: &S) -> DefId {
        if let Some(def_id) = s.with_item_cache(*self, |cache| cache.def_id.clone()) {
            return def_id;
        }
        let def_id = translate_def_id(s, *self);
        s.with_item_cache(*self, |cache| cache.def_id = Some(def_id.clone()));
        def_id
    }
}

#[cfg(feature = "rustc")]
impl From<&DefId> for RDefId {
    fn from<'tcx>(def_id: &DefId) -> Self {
        def_id.to_rust_def_id()
    }
}

// Impl to be able to use hax's `DefId` for many rustc queries.
#[cfg(feature = "rustc")]
impl rustc_middle::query::IntoQueryParam<RDefId> for &DefId {
    fn into_query_param(self) -> RDefId {
        self.into()
    }
}

#[cfg(not(feature = "extract_names_mode"))]
pub type Path = Vec<String>;

#[cfg(all(not(feature = "extract_names_mode"), feature = "rustc"))]
impl std::convert::From<DefId> for Path {
    fn from(v: DefId) -> Vec<String> {
        std::iter::once(&v.krate)
            .chain(v.path.iter().filter_map(|item| match &item.data {
                DefPathItem::TypeNs(s)
                | DefPathItem::ValueNs(s)
                | DefPathItem::MacroNs(s)
                | DefPathItem::LifetimeNs(s) => Some(s),
                _ => None,
            }))
            .cloned()
            .collect()
    }
}

#[cfg(not(feature = "extract_names_mode"))]
pub type GlobalIdent = DefId;

#[cfg(all(not(feature = "extract_names_mode"), feature = "rustc"))]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GlobalIdent> for rustc_hir::def_id::LocalDefId {
    fn sinto(&self, st: &S) -> DefId {
        self.to_def_id().sinto(st)
    }
}

/// Reflects [`rustc_hir::definitions::DefPathData`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(AdtInto, JsonSchema))]
#[cfg_attr(not(feature = "extract_names_mode"), args(<'ctx, S: UnderOwnerState<'ctx>>, from: rustc_hir::definitions::DefPathData, state: S as s))]
pub enum DefPathItem {
    CrateRoot {
        #[cfg_attr(not(feature = "extract_names_mode"), value(s.base().tcx.crate_name(s.owner_id().krate).sinto(s)))]
        name: Symbol,
    },
    Impl,
    ForeignMod,
    Use,
    GlobalAsm,
    TypeNs(Symbol),
    ValueNs(Symbol),
    MacroNs(Symbol),
    LifetimeNs(Symbol),
    Closure,
    Ctor,
    AnonConst,
    OpaqueTy,
    AnonAdt,
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(AdtInto, JsonSchema))]
#[cfg_attr(not(feature = "extract_names_mode"), args(<'a, S: UnderOwnerState<'a>>, from: rustc_hir::definitions::DisambiguatedDefPathData, state: S as s))]
/// Reflects [`rustc_hir::definitions::DisambiguatedDefPathData`]
pub struct DisambiguatedDefPathItem {
    pub data: DefPathItem,
    pub disambiguator: u32,
}
