use crate::prelude::*;

/// Meta-informations about an `impl<GENERICS[: PREDICATES]> TRAIT for
/// TYPE where PREDICATES {}`
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ImplInfos {
    pub generics: TyGenerics,
    pub clauses: Vec<(Clause, Span)>,
    pub typ: Ty,
    pub trait_ref: Option<TraitRef>,
}
