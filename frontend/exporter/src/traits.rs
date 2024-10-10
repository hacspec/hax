use crate::prelude::*;

#[cfg(feature = "rustc")]
mod resolution;
#[cfg(feature = "rustc")]
mod utils;
#[cfg(feature = "rustc")]
pub use utils::erase_and_norm;

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: resolution::PathChunk<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprPathChunk {
    AssocItem {
        item: AssocItem,
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        /// The nth predicate returned by `tcx.item_bounds`.
        index: usize,
    },
    Parent {
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        /// The nth predicate returned by `tcx.predicates_of`.
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
        /// `tcx.predicates_defined_on` starting from the parentmost item. If the item is an opaque
        /// type, we also append the predicates from `explicit_item_bounds` to this list.
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
    /// A list of `ImplExpr`s required to fully specify the trait references in `impl`.
    pub args: Vec<ImplExpr>,
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
    let tcx = s.base().tcx;
    let mut searcher = resolution::PredicateSearcher::new_for_owner(tcx, s.owner_id());
    match searcher.resolve(&trait_ref, &warn) {
        Ok(x) => x.sinto(s),
        Err(e) => crate::fatal!(s, "{}", e),
    }
}

/// Solve the trait obligations for a specific item use (for example, a method call, an ADT, etc.).
///
/// [predicates]: optional predicates, in case we want to solve custom predicates (instead of the
/// ones returned by [TyCtxt::predicates_defined_on].
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: rustc_hir::def_id::DefId,
    generics: rustc_middle::ty::GenericArgsRef<'tcx>,
    predicates: Option<rustc_middle::ty::GenericPredicates<'tcx>>,
) -> Vec<ImplExpr> {
    let tcx = s.base().tcx;
    let param_env = s.param_env();

    let mut impl_exprs = Vec::new();

    // Lookup the predicates and iter through them: we want to solve all the
    // trait requirements.
    // IMPORTANT: we use [TyCtxt::predicates_defined_on] and not [TyCtxt::predicated_of]
    let predicates = match predicates {
        None => tcx.predicates_defined_on(def_id),
        Some(preds) => preds,
    };
    for (pred, _) in predicates.predicates {
        // Explore only the trait predicates
        if let Some(trait_clause) = pred.as_trait_clause() {
            let poly_trait_ref = trait_clause.map_bound(|clause| clause.trait_ref);
            // Apply the substitution
            let poly_trait_ref =
                rustc_middle::ty::EarlyBinder::bind(poly_trait_ref).instantiate(tcx, generics);
            // Warning: this erases regions. We don't really have a way to normalize without
            // erasing regions, but this may cause problems in trait solving if there are trait
            // impls that include `'static` lifetimes.
            let poly_trait_ref = tcx
                .try_normalize_erasing_regions(param_env, poly_trait_ref)
                .unwrap_or(poly_trait_ref);
            let impl_expr = solve_trait(s, poly_trait_ref);
            impl_exprs.push(impl_expr);
        }
    }
    impl_exprs
}

/// Retrieve the `Self: Trait` clause for a trait associated item.
#[cfg(feature = "rustc")]
pub fn self_clause_for_item<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    assoc: &rustc_middle::ty::AssocItem,
    generics: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<ImplExpr> {
    let tcx = s.base().tcx;

    // Retrieve the trait
    let tr_def_id = tcx.trait_of_item(assoc.def_id)?;

    // Create the reference to the trait
    use rustc_middle::ty::TraitRef;
    let tr_generics = tcx.generics_of(tr_def_id);
    let generics = generics.truncate_to(tcx, tr_generics);
    let tr_ref = TraitRef::new(tcx, tr_def_id, generics);
    let tr_ref = rustc_middle::ty::Binder::dummy(tr_ref);

    // Solve
    Some(solve_trait(s, tr_ref))
}
