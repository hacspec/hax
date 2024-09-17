use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(transparent)]
/// A `PredicateId` is a unique identifier for a clause or a
/// predicate. It is computed by hashing predicates and clause in a
/// uniform and deterministic way.
pub struct PredicateId(u64);

#[cfg(feature = "rustc")]
mod rustc {
    use super::*;
    impl<'tcx> Binder<PredicateKind> {
        #[tracing::instrument(level = "trace")]
        pub fn predicate_id(&self) -> PredicateId {
            // Here, we need to be careful about not hashing a `crate::Predicate`,
            // but `crate::Binder<crate::PredicateKind>` instead,
            // otherwise we would get into a infinite recursion.
            PredicateId(deterministic_hash(self))
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
        use std::hash::BuildHasher;
        use std::hash::BuildHasherDefault;
        <BuildHasherDefault<DeterministicHasher<DefaultHasher>>>::default().hash_one(x)
    }
}
