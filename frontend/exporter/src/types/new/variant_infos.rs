use crate::prelude::*;
use crate::sinto_as_usize;

/// Describe the kind of a variant
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum VariantKind {
    /// The variant is the only variant of a `struct` type
    Struct {
        /// Are the fields on this struct all named?
        named: bool,
    },
    /// The variant is the only variant of a `union` type
    Union,
    /// The variant is one of the many variants of a `enum` type
    Enum {
        /// The index of this variant in the `enum`
        index: VariantIdx,
        /// Are the fields on this struct all named?
        named: bool,
    },
}

sinto_as_usize!(rustc_target::abi, VariantIdx);

/// Describe a variant
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariantInformations {
    pub type_namespace: DefId,

    pub typ: DefId,
    pub variant: DefId,
    pub kind: VariantKind,
}
