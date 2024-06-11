use crate::prelude::*;

#[derive(
    Copy, Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
#[serde(transparent)]
/// A `PredicateId` is a unique identifier for a clause or a
/// predicate. It is computed by hashing predicates and clause in a
/// uniform and deterministic way.
pub struct PredicateId(u64);

#[cfg(feature = "full")]
mod full {
    use super::*;
    use rustc_middle::ty;
    /// Implemented by anything that can be assimilated to a predicate.
    pub trait IntoPredicateId<'tcx, S: UnderOwnerState<'tcx>> {
        /// Compute a consistent `PredicateId`
        fn predicate_id(&self, s: &S) -> PredicateId;
    }

    impl<'tcx, S: UnderOwnerState<'tcx>> IntoPredicateId<'tcx, S> for ty::Clause<'tcx> {
        fn predicate_id(&self, s: &S) -> PredicateId {
            self.as_predicate().predicate_id(s)
        }
    }

    impl<'tcx, S: UnderOwnerState<'tcx>> IntoPredicateId<'tcx, S> for ty::Predicate<'tcx> {
        fn predicate_id(&self, s: &S) -> PredicateId {
            // Here, we need to be careful about not hashing a `crate::Predicate`,
            // but `crate::Binder<crate::PredicateKind>` instead,
            // otherwise we would get into a infinite recursion.
            let poly_kind: Binder<PredicateKind> = self.kind().sinto(s);
            PredicateId(deterministic_hash(&poly_kind))
        }
    }

    impl<'tcx, S: UnderOwnerState<'tcx>> IntoPredicateId<'tcx, S> for ty::PolyTraitPredicate<'tcx> {
        fn predicate_id(&self, s: &S) -> PredicateId {
            use ty::ToPredicate;
            let predicate: ty::Predicate<'tcx> = (*self).to_predicate(s.base().tcx);
            predicate.predicate_id(s)
        }
    }

    /// A `PredicateId` can be mapped to itself via SInto. This is useful
    /// for mirroring the type [`traits::search_clause::PathChunk`] as
    /// [`traits::ImplExprPathChunk`].
    impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, PredicateId> for PredicateId {
        fn sinto(&self, _s: &S) -> PredicateId {
            *self
        }
    }

    /// We need identifiers that are stable across different
    /// architectures, different paths (which are observable from
    /// `Span`s), etc.
    /// Rustc's stable hash is not doing what we want here: it is sensible
    /// to the environment. Instead, we first `sinto` and then hash with
    /// `deterministic_hash` below.
    fn deterministic_hash<T: std::hash::Hash>(x: &T) -> u64 {
        use crate::deterministic_hash::DeterministicHasher;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;
        let mut hasher = DeterministicHasher::new(DefaultHasher::new());
        x.hash(&mut hasher);
        hasher.finish()
    }
}
#[cfg(feature = "full")]
pub use full::*;
