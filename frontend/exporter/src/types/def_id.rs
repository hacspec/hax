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

pub use serde::{Deserialize, Serialize};

#[cfg(not(feature = "extract_names_mode"))]
use crate::{AdtInto, BaseState, JsonSchema, SInto};

pub type Symbol = String;

#[derive(Clone, Debug, Serialize, Deserialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(not(feature = "extract_names_mode"), derive(AdtInto, JsonSchema))]
#[cfg_attr(not(feature = "extract_names_mode"), args(<'a, S: BaseState<'a>>, from: rustc_hir::definitions::DisambiguatedDefPathData, state: S as s))]
/// Reflects [`rustc_hir::definitions::DisambiguatedDefPathData`]
pub struct DisambiguatedDefPathItem {
    pub data: DefPathItem,
    pub disambiguator: u32,
}

/// Reflects [`rustc_hir::def_id::DefId`]
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
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
}

/// Reflects [`rustc_hir::definitions::DefPathData`]
#[derive(Clone, Debug, Serialize, Deserialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
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
}
