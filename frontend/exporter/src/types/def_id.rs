use crate::{AdtInto, JsonSchema};
pub use serde::{Deserialize, Serialize};

#[cfg(feature = "full")]
use crate::{BaseState, SInto};

pub type Symbol = String;

#[derive(
    Clone, Debug, Serialize, Deserialize, Hash, PartialEq, Eq, PartialOrd, Ord, AdtInto, JsonSchema,
)]
#[args(<'a, S: BaseState<'a>>, from: rustc_hir::definitions::DisambiguatedDefPathData, state: S as s)]
/// Reflects [`rustc_hir::definitions::DisambiguatedDefPathData`]
pub struct DisambiguatedDefPathItem {
    pub data: DefPathItem,
    pub disambiguator: u32,
}

/// Reflects [`rustc_hir::def_id::DefId`]
#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialOrd, Ord, JsonSchema)]
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
#[derive(
    Clone, Debug, AdtInto, JsonSchema, Serialize, Deserialize, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
#[args(<'ctx, S: BaseState<'ctx>>, from: rustc_hir::definitions::DefPathData, state: S as state)]
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
    ClosureExpr,
    Ctor,
    AnonConst,
    ImplTrait,
    ImplTraitAssocTy,
}

impl std::hash::Hash for DefId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let DefId {
            krate,
            path,
            index: _, // intentionally discarding index
        } = self;
        krate.hash(state);
        path.hash(state);
    }
}

impl std::cmp::PartialEq for DefId {
    fn eq(&self, other: &Self) -> bool {
        self.krate.eq(&other.krate) && self.path.eq(&other.path)
    }
}

impl DefId {
    pub fn serialize_compact(&self) -> String {
        use itertools::Itertools;
        [self.krate.clone()]
            .into_iter()
            .chain(self.path.iter().map(|item| item.serialize_compact()))
            .join("::")
    }
    pub fn deserialize_compact(s: &str) -> Option<Self> {
        const DUMMY_INDEX: (u32, u32) = (0, 0);
        match s.split("::").collect::<Vec<_>>().as_slice() {
            [krate, path @ ..] => Some(Self {
                krate: krate.to_string(),
                path: path
                    .iter()
                    .map(|item| DisambiguatedDefPathItem::deserialize_compact(item))
                    .collect::<Option<Vec<_>>>()?,
                index: DUMMY_INDEX,
            }),
            _ => None,
        }
    }
}
impl DisambiguatedDefPathItem {
    fn serialize_compact(&self) -> String {
        let data = self.data.serialize_compact();
        if self.disambiguator == 0 {
            data
        } else {
            format!("{data}#{}", self.disambiguator)
        }
    }
    fn deserialize_compact(s: &str) -> Option<Self> {
        let mut disambiguator = 0;
        let mut data_string = s;
        if let Some((s, num)) = s.split_once("#") {
            if let Ok(num) = num.parse::<u32>() {
                disambiguator = num;
                data_string = s;
            }
        }
        Some(DisambiguatedDefPathItem {
            data: DefPathItem::deserialize_compact(data_string)?,
            disambiguator,
        })
    }
}

mod tags {
    #![allow(non_upper_case_globals)]
    pub const CrateRoot: &str = "CrateRoot";
    pub const Impl: &str = "Impl";
    pub const ForeignMod: &str = "ForeignMod";
    pub const Use: &str = "Use";
    pub const GlobalAsm: &str = "GlobalAsm";
    pub const TypeNs: &str = "ty";
    pub const ValueNs: &str = "val";
    pub const MacroNs: &str = "macro";
    pub const LifetimeNs: &str = "lt";
    pub const ClosureExpr: &str = "Closure";
    pub const Ctor: &str = "Ctor";
    pub const AnonConst: &str = "AnonConst";
    pub const ImplTrait: &str = "ImplTrait";
    pub const ImplTraitAssocTy: &str = "ImplTraitAssocTy";
}
const SEP: &str = "~";
impl DefPathItem {
    fn serialize_compact(&self) -> String {
        match self {
            Self::CrateRoot => format!("{}{SEP}", tags::CrateRoot),
            Self::Impl => format!("{}{SEP}", tags::Impl),
            Self::ForeignMod => format!("{}{SEP}", tags::ForeignMod),
            Self::Use => format!("{}{SEP}", tags::Use),
            Self::GlobalAsm => format!("{}{SEP}", tags::GlobalAsm),
            Self::TypeNs(s) => format!("{}{SEP}{s}", tags::TypeNs),
            Self::ValueNs(s) => format!("{}{SEP}{s}", tags::ValueNs),
            Self::MacroNs(s) => format!("{}{SEP}{s}", tags::MacroNs),
            Self::LifetimeNs(s) => format!("{}{SEP}{s}", tags::LifetimeNs),
            Self::ClosureExpr => format!("{}{SEP}", tags::ClosureExpr),
            Self::Ctor => format!("{}{SEP}", tags::Ctor),
            Self::AnonConst => format!("{}{SEP}", tags::AnonConst),
            Self::ImplTrait => format!("{}{SEP}", tags::ImplTrait),
            Self::ImplTraitAssocTy => format!("{}{SEP}", tags::ImplTraitAssocTy),
        }
    }
    fn deserialize_compact(s: &str) -> Option<Self> {
        Some(if let Some((tag, s)) = s.split_once(SEP) {
            if s.is_empty() {
                match tag {
                    tags::CrateRoot => Self::CrateRoot,
                    tags::Impl => Self::Impl,
                    tags::ForeignMod => Self::ForeignMod,
                    tags::Use => Self::Use,
                    tags::GlobalAsm => Self::GlobalAsm,
                    tags::ClosureExpr => Self::ClosureExpr,
                    tags::Ctor => Self::Ctor,
                    tags::AnonConst => Self::AnonConst,
                    tags::ImplTrait => Self::ImplTrait,
                    tags::ImplTraitAssocTy => Self::ImplTraitAssocTy,
                    _ => None?,
                }
            } else {
                let s = s.to_string();
                match tag {
                    tags::ValueNs => Self::ValueNs(s),
                    tags::TypeNs => Self::TypeNs(s),
                    tags::MacroNs => Self::MacroNs(s),
                    tags::LifetimeNs => Self::LifetimeNs(s),
                    _ => None?,
                }
            }
        } else {
            None?
        })
    }
}
