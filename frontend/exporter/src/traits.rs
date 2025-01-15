use crate::prelude::*;

#[cfg(feature = "rustc")]
mod resolution;
#[cfg(feature = "rustc")]
mod utils;
#[cfg(feature = "rustc")]
pub use utils::{
    erase_and_norm, implied_predicates, predicates_defined_on, required_predicates, self_predicate,
};

#[cfg(feature = "rustc")]
pub use resolution::PredicateSearcher;
#[cfg(feature = "rustc")]
use rustc_middle::ty;
#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::PathChunk<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprPathChunk {
    AssocItem {
        item: AssocItem,
        /// The arguments provided to the item (for GATs).
        generic_args: Vec<GenericArg>,
        /// The impl exprs that must be satisfied to apply the given arguments to the item. E.g.
        /// `T: Clone` in the following example:
        /// ```ignore
        /// trait Foo {
        ///     type Type<T: Clone>: Debug;
        /// }
        /// ```
        impl_exprs: Vec<ImplExpr>,
        /// The implemented predicate.
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        /// The index of this predicate in the list returned by `implied_predicates`.
        index: usize,
    },
    Parent {
        /// The implemented predicate.
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        /// The index of this predicate in the list returned by `implied_predicates`.
        index: usize,
    },
}

/// The source of a particular trait implementation. Most often this is either `Concrete` for a
/// concrete `impl Trait for Type {}` item, or `LocalBound` for a context-bound `where T: Trait`.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::ImplExprAtom<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprAtom {
    /// A concrete `impl Trait for Type {}` item.
    Concrete {
        #[from(def_id)]
        id: GlobalIdent,
        generics: Vec<GenericArg>,
        /// The impl exprs that prove the clauses on the impl.
        impl_exprs: Vec<ImplExpr>,
    },
    /// A context-bound clause like `where T: Trait`.
    LocalBound {
        #[not_in_source]
        #[value({
            let Self::LocalBound { predicate, .. } = self else { unreachable!() };
            predicate.sinto(s).id
        })]
        predicate_id: PredicateId,
        /// The nth (non-self) predicate found for this item. We use predicates from
        /// `required_predicates` starting from the parentmost item.
        index: usize,
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// The implicit `Self: Trait` clause present inside a `trait Trait {}` item.
    // TODO: should we also get that clause for trait impls?
    SelfImpl {
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// `dyn Trait` is a wrapped value with a virtual table for trait
    /// `Trait`.  In other words, a value `dyn Trait` is a dependent
    /// triple that gathers a type τ, a value of type τ and an
    /// instance of type `Trait`.
    /// `dyn Trait` implements `Trait` using a built-in implementation; this refers to that
    /// built-in implementation.
    Dyn,
    /// A built-in trait whose implementation is computed by the compiler, such as `Sync`.
    Builtin { r#trait: Binder<TraitRef> },
    /// An error happened while resolving traits.
    Error(String),
}

/// An `ImplExpr` describes the full data of a trait implementation. Because of generics, this may
/// need to combine several concrete trait implementation items. For example, `((1u8, 2u8),
/// "hello").clone()` combines the generic implementation of `Clone` for `(A, B)` with the
/// concrete implementations for `u8` and `&str`, represented as a tree.
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema, AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::ImplExpr<'tcx>, state: S as s)]
pub struct ImplExpr {
    /// The trait this is an impl for.
    pub r#trait: Binder<TraitRef>,
    /// The kind of implemention of the root of the tree.
    pub r#impl: ImplExprAtom,
}

/// Given a clause `clause` in the context of some impl block `impl_did`, susbts correctly `Self`
/// from `clause` and (1) derive a `Clause` and (2) resolve an `ImplExpr`.
#[cfg(feature = "rustc")]
pub fn super_clause_to_clause_and_impl_expr<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    impl_did: rustc_span::def_id::DefId,
    clause: rustc_middle::ty::Clause<'tcx>,
    span: rustc_span::Span,
) -> Option<(Clause, ImplExpr, Span)> {
    use rustc_middle::ty::ToPolyTraitRef;
    let tcx = s.base().tcx;
    let impl_trait_ref = tcx
        .impl_trait_ref(impl_did)
        .map(|binder| rustc_middle::ty::Binder::dummy(binder.instantiate_identity()))?;
    let original_predicate_id = {
        // We don't want the id of the substituted clause id, but the
        // original clause id (with, i.e., `Self`)
        let s = &with_owner_id(s.base(), (), (), impl_trait_ref.def_id());
        clause.sinto(s).id
    };
    let new_clause = clause.instantiate_supertrait(tcx, impl_trait_ref);
    let impl_expr = solve_trait(
        s,
        new_clause
            .as_predicate()
            .as_trait_clause()?
            .to_poly_trait_ref(),
    );
    let mut new_clause_no_binder = new_clause.sinto(s);
    new_clause_no_binder.id = original_predicate_id;
    Some((new_clause_no_binder, impl_expr, span.sinto(s)))
}

/// This is the entrypoint of the solving.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s))]
pub fn solve_trait<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> ImplExpr {
    let warn = |msg: &str| {
        if !s.base().ty_alias_mode {
            crate::warning!(s, "{}", msg)
        }
    };
    if let Some(impl_expr) = s.with_cache(|cache| cache.impl_exprs.get(&trait_ref).cloned()) {
        return impl_expr;
    }
    let resolved = s.with_cache(|cache| {
        cache
            .predicate_searcher
            .get_or_insert_with(|| PredicateSearcher::new_for_owner(s.base().tcx, s.owner_id()))
            .resolve(&trait_ref, &warn)
    });
    let impl_expr = match resolved {
        Ok(x) => x.sinto(s),
        Err(e) => crate::fatal!(s, "{}", e),
    };
    s.with_cache(|cache| cache.impl_exprs.insert(trait_ref, impl_expr.clone()));
    impl_expr
}

/// Solve the trait obligations for a specific item use (for example, a method call, an ADT, etc.)
/// in the current context.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_required_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> Vec<ImplExpr> {
    let predicates = required_predicates(s.base().tcx, def_id);
    solve_item_traits_inner(s, generics, predicates)
}

/// Solve the trait obligations for implementing a trait (or for trait associated type bounds) in
/// the current context.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_implied_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> Vec<ImplExpr> {
    let predicates = implied_predicates(s.base().tcx, def_id);
    solve_item_traits_inner(s, generics, predicates)
}

/// Apply the given generics to the provided clauses and resolve the trait references in the
/// current context.
#[cfg(feature = "rustc")]
fn solve_item_traits_inner<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    generics: ty::GenericArgsRef<'tcx>,
    predicates: ty::GenericPredicates<'tcx>,
) -> Vec<ImplExpr> {
    use crate::rustc_middle::ty::ToPolyTraitRef;
    let tcx = s.base().tcx;
    let param_env = s.param_env();
    predicates
        .predicates
        .iter()
        .map(|(clause, _span)| *clause)
        .filter_map(|clause| clause.as_trait_clause())
        .map(|clause| clause.to_poly_trait_ref())
        // Substitute the item generics
        .map(|trait_ref| ty::EarlyBinder::bind(trait_ref).instantiate(tcx, generics))
        // We unfortunately don't have a way to normalize without erasing regions.
        .map(|trait_ref| {
            tcx.try_normalize_erasing_regions(param_env, trait_ref)
                .unwrap_or(trait_ref)
        })
        // Resolve
        .map(|trait_ref| solve_trait(s, trait_ref))
        .collect()
}

/// Retrieve the `Self: Trait` clause for a trait associated item.
#[cfg(feature = "rustc")]
pub fn self_clause_for_item<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    assoc: &rustc_middle::ty::AssocItem,
    generics: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<ImplExpr> {
    use rustc_middle::ty::EarlyBinder;
    let tcx = s.base().tcx;

    let tr_def_id = tcx.trait_of_item(assoc.def_id)?;
    // The "self" predicate in the context of the trait.
    let self_pred = self_predicate(tcx, tr_def_id);
    // Substitute to be in the context of the current item.
    let generics = generics.truncate_to(tcx, tcx.generics_of(tr_def_id));
    let self_pred = EarlyBinder::bind(self_pred).instantiate(tcx, generics);

    // Resolve
    Some(solve_trait(s, self_pred))
}
