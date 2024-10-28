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

#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(AdtInto, JsonSchema))]
#[cfg_attr(not(feature = "extract_names_mode"), args(<'a, S: BaseState<'a>>, from: rustc_hir::definitions::DisambiguatedDefPathData, state: S as s))]
/// Reflects [`rustc_hir::definitions::DisambiguatedDefPathData`]
pub struct DisambiguatedDefPathItem {
    pub data: DefPathItem,
    pub disambiguator: u32,
}

/// Reflects [`rustc_hir::def_id::DefId`]
#[derive_group(Serializers)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(JsonSchema))]
pub struct DefId {
    pub krate: String,
    pub path: Vec<DisambiguatedDefPathItem>,
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
        let DefId {
            krate,
            path,
            index: _,    // intentionally discarding index
            is_local: _, // intentionally discarding is_local
        } = self;
        krate.hash(state);
        path.hash(state);
    }
}

#[cfg(feature = "rustc")]
pub(crate) fn translate_def_id<'tcx, S: BaseState<'tcx>>(s: &S, def_id: RDefId) -> DefId {
    let tcx = s.base().tcx;
    let def_path = tcx.def_path(def_id);
    let krate = tcx.crate_name(def_path.krate);
    DefId {
        path: def_path.data.iter().map(|x| x.sinto(s)).collect(),
        krate: format!("{}", krate),
        index: (
            rustc_hir::def_id::CrateNum::as_u32(def_id.krate),
            rustc_hir::def_id::DefIndex::as_u32(def_id.index),
        ),
        is_local: def_id.is_local(),
    }
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
        let (krate, index) = def_id.index;
        Self {
            krate: rustc_hir::def_id::CrateNum::from_u32(krate),
            index: rustc_hir::def_id::DefIndex::from_u32(index),
        }
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
        std::iter::once(v.krate)
            .chain(v.path.into_iter().filter_map(|item| match item.data {
                DefPathItem::TypeNs(s)
                | DefPathItem::ValueNs(s)
                | DefPathItem::MacroNs(s)
                | DefPathItem::LifetimeNs(s) => Some(s),
                _ => None,
            }))
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
#[cfg_attr(not(feature = "extract_names_mode"), args(<'ctx, S: BaseState<'ctx>>, from: rustc_hir::definitions::DefPathData, state: S as state))]
pub enum DefPathItem {
    CrateRoot,
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
