use rustc_hir::def::DefKind;
use rustc_middle::ty::*;

/// Just like `TyCtxt::predicates_of`, but in the case of a trait or impl item or closures,
/// also includes the predicates defined on the parents. Also this returns the special
/// `Self` clause separately.
pub fn predicates_of_or_above<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: rustc_span::def_id::DefId,
) -> (
    Vec<PolyTraitPredicate<'tcx>>,
    Option<PolyTraitPredicate<'tcx>>,
) {
    use DefKind::*;
    let def_kind = tcx.def_kind(did);

    let (mut predicates, mut self_pred) = match def_kind {
        // These inherit some predicates from their parent.
        AssocTy | AssocFn | AssocConst | Closure => {
            let parent = tcx.parent(did);
            predicates_of_or_above(tcx, parent)
        }
        _ => (vec![], None),
    };

    match def_kind {
        // Don't list the predicates of traits, we already list the `Self` clause from
        // which we can resolve anything needed.
        Trait => {}
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
        | Union => {
            // Only these kinds may reasonably have predicates; we have to filter
            // otherwise calling `predicates_defined_on` may ICE.
            predicates.extend(
                tcx.predicates_defined_on(did)
                    .predicates
                    .iter()
                    .filter_map(|(clause, _span)| clause.as_trait_clause()),
            );
        }
        _ => {}
    }

    // Add some extra predicates that aren't in `predicates_defined_on`.
    match def_kind {
        OpaqueTy => {
            // An opaque type (e.g. `impl Trait`) provides predicates by itself: we need to
            // account for them.
            // TODO: is this still useful? The test that used to require this doesn't anymore.
            predicates.extend(
                tcx.explicit_item_bounds(did)
                    .skip_binder() // Skips an `EarlyBinder`, likely for GATs
                    .iter()
                    .filter_map(|(clause, _span)| clause.as_trait_clause()),
            )
        }
        Trait => {
            // Add the special `Self: Trait` clause.
            // Copied from the code of `tcx.predicates_of()`.
            let self_clause: Clause<'_> = TraitRef::identity(tcx, did).upcast(tcx);
            self_pred = Some(self_clause.as_trait_clause().unwrap());
        }
        _ => {}
    }

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
