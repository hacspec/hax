use crate::prelude::*;

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub struct TraitInfo {
    pub impl_expr: ImplExpr,
    /// All the generics (from before truncating them - see the documentation
    /// for [ParamsInfo]). We store this information mostly for debugging purposes.
    pub all_generics: Vec<GenericArg>,
}

/// Retrieve the trait information, typically for a function call.
/// [ref_def_id]: id of the method being called, the global being used, etc.
/// TODO: rename
pub fn get_trait_info<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    ref_def_id: rustc_hir::def_id::DefId,
    substs: rustc_middle::ty::SubstsRef<'tcx>,
    assoc: &rustc_middle::ty::AssocItem,
) -> (Vec<GenericArg>, TraitInfo) {
    let tcx = s.base().tcx;
    let param_env = tcx.param_env(s.owner_id());

    // Retrieve the trait
    let tr = tcx.trait_of_item(assoc.def_id).unwrap();

    // Create the reference to the trait
    use rustc_middle::ty::TraitRef;
    let tr_ref = TraitRef::new(tcx, tr, substs);
    let tr_ref = rustc_middle::ty::Binder::dummy(tr_ref);

    // Solve
    get_trait_info_for_trait_ref(s, ref_def_id, param_env, tr_ref)
}

pub fn solve_trait<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> ImplExpr {
    trait_ref.impl_expr(s, param_env)
}

/// Retrieve the trait information, typically for a function call.
/// [ref_def_id]: id of the method being called, the global being used, etc.
pub fn get_trait_info_for_trait_ref<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    _ref_def_id: rustc_hir::def_id::DefId,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> (Vec<GenericArg>, TraitInfo) {
    let mut impl_expr = solve_trait(s, param_env, trait_ref);

    // We need to remove the generic arguments which are for the method: we keep
    // the generic arguments which are specific to the trait instance (see the
    // comments in [ParamsInfo]).
    //
    // For instance:
    // ```
    // impl<T> Foo<T> for Bar {
    //   fn baz<U>(...) { ... }
    // }
    //
    // fn test(x: Bar) {
    //   x.baz(...); // Gets desugared to: Foo::baz<Bar, T, U>(x, ...);
    //   ...
    // }
    // ```
    // Above, we want to drop the `Bar` and `T` arguments.

    // Small helper.
    // The source id must refer to:
    // - a top-level impl (which implements the trait)
    // - a trait decl (in the case we can't resolve to a top-level impl)
    // The list of generics is the concatenation of the generics for the
    // top-level impl/the trait ref and the generics for the trait item.
    // We count the number of generics of the top-level impl/the trait decl
    // and split there.
    let update_generics = |src_id: &DefId, x: &mut Vec<GenericArg>| {
        let src_id: rustc_hir::def_id::DefId = src_id.into();
        let params_info = get_params_info(s, src_id);
        let num_trait_generics = params_info.num_generic_params;
        let all_generics = x.clone();
        (all_generics, x.split_off(num_trait_generics))
    };

    let (all_generics, truncated_generics) = match &mut impl_expr.r#impl {
        ImplExprAtom::Concrete {
            ref id,
            ref mut generics,
        } => update_generics(id, generics),
        ImplExprAtom::LocalBound {
            r#trait: trait_ref, ..
        } => update_generics(&trait_ref.value.def_id, &mut trait_ref.value.generic_args),
        ImplExprAtom::Error(..) | ImplExprAtom::Todo(_) => {
            // We do something similar to the local bound case
            let mut trait_ref = trait_ref.sinto(s);
            update_generics(&trait_ref.value.def_id, &mut trait_ref.value.generic_args)
        }
        ImplExprAtom::Builtin { .. } => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl expr:\n{:?}",
                trait_ref,
                impl_expr
            )
            // update_generics(&mut trait_ref.value.generic_args)
        }
        ImplExprAtom::Dyn { .. } => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl expr:\n{:?}",
                trait_ref,
                impl_expr
            )
            // update_generics(&mut trait_ref.value.generic_args)
        }
        ImplExprAtom::FnPointer { .. } => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl expr:\n{:?}",
                trait_ref,
                impl_expr
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
        ImplExprAtom::Closure { .. } => {
            // We don't need to truncate the generics (there shouldn't be any)
            let trait_ref = trait_ref.sinto(s);
            (
                trait_ref.value.generic_args.clone(),
                trait_ref.value.generic_args,
            )
        }
    };

    let info = TraitInfo {
        impl_expr,
        all_generics,
    };
    (truncated_generics, info)
}

/// Solve the trait obligations for a specific item use (for example, a method
/// call, an ADT, etc.).
///
/// [predicates]: optional predicates, in case we want to solve custom predicates
/// (instead of the ones returned by [TyCtxt::predicates_defined_on].
pub fn solve_item_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
    predicates: Option<rustc_middle::ty::GenericPredicates<'tcx>>,
) -> Vec<ImplExpr> {
    let tcx = s.base().tcx;

    let mut impl_exprs = Vec::new();

    // Lookup the predicates and iter through them: we want to solve all the
    // trait requirements.
    // IMPORTANT: we use [TyCtxt::predicates_defined_on] and not [TyCtxt::predicated_of]
    let predicates = match predicates {
        None => tcx.predicates_defined_on(def_id),
        Some(preds) => preds,
    };
    for (pred, _) in predicates.predicates {
        // Apply the substitution
        let pred_kind = subst_binder(tcx, substs, param_env, pred.kind(), true);

        // Just explore the trait predicates
        use rustc_middle::ty::{Clause, PredicateKind};
        if let PredicateKind::Clause(Clause::Trait(trait_pred)) = pred_kind {
            // SH: We also need to introduce a binder here. I'm not sure what we
            // whould bind this with: the variables to bind with are those
            // given by the definition we are exploring, and they should already
            // be in the param environment. So I just wrap in a dummy binder
            // (this also seems to work so far).
            //
            // Also, we can't wrap in a dummy binder if there are escaping bound vars.
            // For now, we fail if there are escaping bound vars.
            // **SH:** I encountered this issue several times, but the "error"
            // clause never made it to the final code. I think it is because it
            // was introduced when computing the "full trait ref" information.
            let trait_ref = trait_pred.trait_ref;
            use crate::rustc_middle::ty::TypeVisitableExt;
            let impl_expr = if trait_ref.has_escaping_bound_vars() {
                // Error
                // TODO: is this case still necessary? Look at how it is done
                // in THIR.
                let msg = format!("{:?} has escaping bound vars", trait_ref);
                let trait_ref = {
                    let tr = trait_ref.sinto(s);
                    TraitRef {
                        def_id: tr.def_id,
                        generic_args: tr.generic_args,
                    }
                };
                let kind = ImplExprAtom::Error(msg);
                ImplExpr {
                    r#impl: kind,
                    // Empty args for now
                    args: Box::new(Vec::new()),
                    trait_ref,
                }
            } else {
                // Ok
                let trait_ref = rustc_middle::ty::Binder::dummy(trait_pred.trait_ref);
                solve_trait(s, param_env, trait_ref)
            };

            impl_exprs.push(impl_expr);
        }
    }
    impl_exprs
}

/// Small helper
///
/// Introducing this to make sure all binders are handled in a consistent manner.
pub(crate) fn subst_early_binder<'tcx, T>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    param_substs: rustc_middle::ty::SubstsRef<'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    value: rustc_middle::ty::EarlyBinder<T>,
    normalize_erase: bool,
) -> T
where
    T: rustc_middle::ty::TypeFoldable<rustc_middle::ty::TyCtxt<'tcx>>,
{
    // SH: Not sure this is the proper way, but it seems to work so far. My reasoning:
    // - I don't know how to get rid of the Binder, because there is no
    //   Binder::subst method.
    // - However I notice that EarlyBinder is just a wrapper (it doesn't
    //   contain any information) and comes with substitution methods.
    // So I skip the Binder, wrap the value in an EarlyBinder and apply
    // the substitution.
    // Remark: there is also EarlyBinder::subst(...)

    // Apply the substitution.
    //
    // **Remark:** we used to always call [TyCtxt::subst_and_normalize_erasing_regions],
    // but this normalizes the types, leading to issues. For instance here:
    // ```
    // pub fn f<T: Foo<S = U::S>, U: Foo>() {}
    // ```
    // The issue is that T refers `U : Foo` before the clause is
    // defined. If we normalize the types in the items of `T : Foo`,
    // when exploring the items of `Foo<T>` we find the clause
    // `Sized<U::S>` (instead of `Sized<T::S>`) because `T::S` has
    // been normalized to `U::S`. This can be problematic when
    // solving the parameters.
    if normalize_erase {
        tcx.subst_and_normalize_erasing_regions(param_substs, param_env, value)
    } else {
        // Remark: in more recent versions of the compiler: [instantiate]
        value.subst(tcx, param_substs)
    }
}

/// Small helper.
///
/// Introducing this to make sure all binders are handled in a consistent manner.
///
/// [normalize_erase]: should we normalize the types and erase the regions?
pub(crate) fn subst_binder<'tcx, T>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    param_substs: rustc_middle::ty::SubstsRef<'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    value: rustc_middle::ty::Binder<'tcx, T>,
    normalize_erase: bool,
) -> T
where
    T: rustc_middle::ty::TypeFoldable<rustc_middle::ty::TyCtxt<'tcx>>,
{
    // SH: Not sure this is the proper way, but it seems to work so far. My reasoning:
    // - I don't know how to get rid of the Binder, because there is no
    //   Binder::subst method.
    // - However I notice that EarlyBinder is just a wrapper (it doesn't
    //   contain any information) and comes with substitution methods.
    // So I skip the Binder, wrap the value in an EarlyBinder and apply
    // the substitution.
    // Remark: there is also EarlyBinder::subst(...)
    let value = rustc_middle::ty::EarlyBinder::bind(value.skip_binder());
    subst_early_binder(tcx, param_substs, param_env, value, normalize_erase)
}

/// We use this to store information about the parameters in parent blocks.
/// This is necessary because when querying the generics of a definition,
/// rustc gives us *all* the generics used in this definition, including
/// those coming from the outer impl block.
///
/// For instance:
/// ```text
/// impl Foo<T> {
///         ^^^
///       outer block generics
///   fn bar<U>(...)  { ... }
///         ^^^
///       generics local to the function bar
/// }
/// ```
///
/// `TyCtxt.generics_of(bar)` gives us: `[T, U]`.
///
/// We however sometimes need to make a distinction between those two kinds
/// of generics, in particular when manipulating trait instances. For instance:
///
/// ```text
/// impl<T> Foo for Bar<T> {
///   fn baz<U>(...)  { ... }
/// }
///
/// fn test(...) {
///    // Here:
///    x.baz(...);
///    // We should refer to this call as:
///    // > Foo<T>::baz<U>(...)
///    //
///    // If baz hadn't been a method implementation of a trait,
///    // we would have refered to it as:
///    // > baz<T, U>(...)
///    //
///    // The reason is that with traits, we refer to the whole
///    // trait implementation (as if it were a structure), then
///    // pick a specific method inside (as if projecting a field
///    // from a structure).
/// }
/// ```
///
/// **Remark**: Rust only allows refering to the generics of the **immediately**
/// outer block. For this reason, when we need to store the information about
/// the generics of the outer block(s), we need to do it only for one level
/// (this definitely makes things simpler).
/// **Additional remark**: it is not possible to directly write an impl block
/// or a trait definition inside an impl/trait block. However it is possible
/// to define an impl/trait inside a function, which can itself be inside a
/// block, leading to nested impl blocks.
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ParamsInfo {
    /// The total number of generic parameters (regions + types + consts).
    /// We do not consider the trait clauses as generic parameters.
    pub num_generic_params: usize,
    pub num_region_params: usize,
    pub num_type_params: usize,
    pub num_const_generic_params: usize,
    pub num_trait_clauses: usize,
    pub num_regions_outlive: usize,
    pub num_types_outlive: usize,
    pub num_trait_type_constraints: usize,
}

/// Compute the parameters information for a definition. See [ParamsInfo].
pub fn get_params_info<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    def_id: rustc_hir::def_id::DefId,
) -> ParamsInfo {
    let tcx = s.base().tcx;

    // Compute the number of generics
    let mut num_region_params = 0;
    let mut num_type_params = 0;
    let mut num_const_generic_params = 0;
    let mut num_regions_outlive = 0;
    let mut num_types_outlive = 0;
    let mut num_trait_type_constraints = 0;

    let generics = tcx.generics_of(def_id);
    let num_generic_params = generics.params.len();
    use rustc_middle::ty::GenericParamDefKind;
    for param in &generics.params {
        match param.kind {
            GenericParamDefKind::Lifetime => num_region_params += 1,
            GenericParamDefKind::Type { .. } => num_type_params += 1,
            GenericParamDefKind::Const { .. } => num_const_generic_params += 1,
        }
    }

    // Compute the number of trait clauses
    let mut num_trait_clauses = 0;
    // **IMPORTANT**: we do NOT want to [TyCtxt::predicates_of].
    // If we use [TyCtxt::predicates_of] on a trait `Foo`, we get an
    // additional predicate `Self : Foo` (i.e., the trait requires itself),
    // which is not what we want.
    let preds = tcx.predicates_defined_on(def_id);
    for (pred, _) in preds.predicates {
        use rustc_middle::ty::{Clause, PredicateKind};
        match &pred.kind().skip_binder() {
            PredicateKind::Clause(Clause::Trait(_)) => num_trait_clauses += 1,
            PredicateKind::Clause(Clause::RegionOutlives(_)) => num_regions_outlive += 1,
            PredicateKind::Clause(Clause::TypeOutlives(_)) => num_types_outlive += 1,
            PredicateKind::Clause(Clause::Projection(_)) => num_trait_type_constraints += 1,
            _ => (),
        }
    }

    ParamsInfo {
        num_generic_params,
        num_region_params,
        num_type_params,
        num_const_generic_params,
        num_trait_clauses,
        num_regions_outlive,
        num_types_outlive,
        num_trait_type_constraints,
    }
}

/// Compute the parameters information for a definition's parent. See [ParamsInfo].
pub fn get_parent_params_info<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    def_id: rustc_hir::def_id::DefId,
) -> Option<ParamsInfo> {
    s.base()
        .tcx
        .generics_of(def_id)
        .parent
        .map(|parent_id| get_params_info(s, parent_id))
}
