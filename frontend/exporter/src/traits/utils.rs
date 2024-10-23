//! Each item can involve three kinds of predicates:
//! - input aka required predicates: the predicates required to mention the item. These are usually `where`
//!   clauses (or equivalent) on the item:
//! ```ignore
//! struct Foo<T: Clone> { ... }
//! trait Foo<T> where T: Clone { ... }
//! fn function<I>() where I: Iterator, I::Item: Clone { ... }
//! ```
//! - output aka implied predicates: the predicates that are implied by the presence of this item in a
//!   signature. This is mostly trait parent predicates:
//! ```ignore
//! trait Foo: Clone { ... }
//! fn bar<T: Foo>() {
//!   // from `T: Foo` we can deduce `T: Clone`
//! }
//! ```
//!   This could also include implied predicates such as `&'a T` implying `T: 'a` but we don't
//!   consider these.
//! - "self" predicate: that's the special `Self: Trait` predicate in scope within a trait
//!   declaration or implementation for trait `Trait`.
//!
//! Note that within a given item the polarity is reversed: input predicates are the ones that can
//! be assumed to hold and output predicates must be proven to hold. The "self" predicate is both
//! assumed and proven within an impl block, and just assumed within a trait declaration block.
//!
//! The current implementation considers all predicates on traits to be outputs, which has the
//! benefit of reducing the size of signatures. Moreover, the rules on which bounds are required vs
//! implied are subtle. We may change this if this proves to be a problem.
use rustc_hir::def::DefKind;
use rustc_middle::ty::*;
use rustc_span::def_id::DefId;

/// The predicates that must hold to mention this item.
pub fn required_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> impl Iterator<Item = Clause<'tcx>> {
    use DefKind::*;
    match tcx.def_kind(def_id) {
        AssocConst
        | AssocFn
        | AssocTy
        | Const
        | Enum
        | Fn
        | ForeignTy
        | Impl { .. }
        | OpaqueTy
        | Static { .. }
        | Struct
        | TraitAlias
        | TyAlias
        | Union => Some(
            tcx.predicates_defined_on(def_id)
                .predicates
                .iter()
                .map(|(clause, _span)| *clause),
        ),
        // We consider all predicates on traits to be outputs
        Trait => None,
        // `predicates_defined_on ICEs on other def kinds.
        _ => None,
    }
    .into_iter()
    .flatten()
}

/// The special "self" predicate on a trait.
pub fn self_predicate<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<PolyTraitRef<'tcx>> {
    use DefKind::*;
    match tcx.def_kind(def_id) {
        // Copied from the code of `tcx.predicates_of()`.
        Trait => Some(Binder::dummy(TraitRef::identity(tcx, def_id))),
        _ => None,
    }
}

/// The predicates that can be deduced from the presence of this item in a signature. We only
/// consider predicates implied by traits here, not implied bounds such as `&'a T` implying `T:
/// 'a`.
pub fn implied_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> impl Iterator<Item = Clause<'tcx>> {
    use DefKind::*;
    match tcx.def_kind(def_id) {
        // We consider all predicates on traits to be outputs
        Trait => tcx
            .predicates_defined_on(def_id)
            .predicates
            .iter()
            .map(|(clause, _span)| *clause)
            .collect::<Vec<_>>(),
        AssocTy => tcx
            // TODO: `item_bounds` contains parent traits, use `explicit_item_bounds` instead.
            .item_bounds(def_id)
            .instantiate_identity()
            .iter()
            .collect(),
        _ => vec![],
    }
    .into_iter()
}

/// Accumulates the `required_predicates` of this item and its parents, starting from the parents.
/// Also returns the special `Self` clause separately.
pub fn predicates_of_or_above<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (
    Vec<PolyTraitPredicate<'tcx>>,
    Option<PolyTraitPredicate<'tcx>>,
) {
    use DefKind::*;
    let def_kind = tcx.def_kind(def_id);

    let (mut predicates, self_pred) = match def_kind {
        // These inherit some predicates from their parent.
        AssocTy | AssocFn | AssocConst | Closure => {
            let parent = tcx.parent(def_id);
            predicates_of_or_above(tcx, parent)
        }
        _ => {
            let self_pred = self_predicate(tcx, def_id).map(|clause| clause.upcast(tcx));
            (vec![], self_pred)
        }
    };

    predicates
        .extend(required_predicates(tcx, def_id).filter_map(|clause| clause.as_trait_clause()));

    (predicates, self_pred)
}

/// Erase all regions. Largely copied from `tcx.erase_regions`.
pub fn erase_all_regions<'tcx, T>(tcx: TyCtxt<'tcx>, value: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>>,
{
    use rustc_middle::ty;
    struct RegionEraserVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
    }

    impl<'tcx> TypeFolder<TyCtxt<'tcx>> for RegionEraserVisitor<'tcx> {
        fn cx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
            ty.super_fold_with(self)
        }

        fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
        where
            T: TypeFoldable<TyCtxt<'tcx>>,
        {
            // Empty the binder
            Binder::dummy(t.skip_binder().fold_with(self))
        }

        fn fold_region(&mut self, _r: ty::Region<'tcx>) -> ty::Region<'tcx> {
            // We erase bound regions despite it being possibly incorrect. `for<'a> fn(&'a
            // ())` and `fn(&'free ())` are different types: they may implement different
            // traits and have a different `TypeId`. It's unclear whether this can cause us
            // to select the wrong trait reference.
            self.tcx.lifetimes.re_erased
        }
    }
    value.fold_with(&mut RegionEraserVisitor { tcx })
}

// Lifetimes are irrelevant when resolving instances.
pub fn erase_and_norm<'tcx, T>(tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>, x: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>> + Copy,
{
    erase_all_regions(
        tcx,
        tcx.try_normalize_erasing_regions(param_env, x).unwrap_or(x),
    )
}
