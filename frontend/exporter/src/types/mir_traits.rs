use crate::prelude::*;

/// Retrieve the trait information, typically for a function call.
/// TODO: rename
pub fn get_trait_info<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    substs: rustc_middle::ty::SubstsRef<'tcx>,
    assoc: &rustc_middle::ty::AssocItem,
) -> ImplExpr {
    let tcx = s.base().tcx;
    let param_env = tcx.param_env(s.owner_id());

    // Retrieve the trait
    let tr_def_id = tcx.trait_of_item(assoc.def_id).unwrap();

    // Create the reference to the trait
    use rustc_middle::ty::TraitRef;
    let tr_ref = TraitRef::new(tcx, tr_def_id, substs);
    let tr_ref = rustc_middle::ty::Binder::dummy(tr_ref);

    // Solve
    solve_trait(s, param_env, tr_ref)
}

pub fn solve_trait<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> ImplExpr {
    let mut impl_expr = trait_ref.impl_expr(s, param_env);
    // TODO: this is a bug in hax: in case of method calls, the trait ref
    // contains the generics for the trait ref + the generics for the method
    let trait_def_id: rustc_hir::def_id::DefId = (&impl_expr.r#trait.def_id).into();
    let params_info = get_params_info(s, trait_def_id);
    impl_expr
        .r#trait
        .generic_args
        .truncate(params_info.num_generic_params);
    impl_expr
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
        let pred_kind = pred.kind();
        // Apply the substitution
        let bare_pred_kind = {
            // SH: Not sure this is the proper way, but it seems to work so far. My reasoning:
            // - I don't know how to get rid of the Binder, because there is no
            //   Binder::subst method.
            // - However I notice that EarlyBinder is just a wrapper (it doesn't
            //   contain any information) and comes with substitution methods.
            // So I skip the Binder, wrap the value in an EarlyBinder and apply
            // the substitution.
            // Warning: this removes the binder; we need to add it back to avoid escaping bound
            // variables.
            // Remark: there is also EarlyBinder::subst(...)
            let value = rustc_middle::ty::EarlyBinder::bind(pred_kind.skip_binder());
            tcx.subst_and_normalize_erasing_regions(substs, param_env, value)
        };

        // Explore only the trait predicates
        use rustc_middle::ty::ClauseKind;
        if let ClauseKind::Trait(trait_pred) = bare_pred_kind {
            // Rewrap the now-substituted kind with the original binder. Substitution dealt with
            // early bound variables; this binds late bound ones.
            let trait_ref = pred_kind.rebind(trait_pred.trait_ref);
            let impl_expr = solve_trait(s, param_env, trait_ref);
            impl_exprs.push(impl_expr);
        }
    }
    impl_exprs
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
        use rustc_middle::ty::ClauseKind;
        match &pred.kind().skip_binder() {
            ClauseKind::Trait(_) => num_trait_clauses += 1,
            ClauseKind::RegionOutlives(_) => num_regions_outlive += 1,
            ClauseKind::TypeOutlives(_) => num_types_outlive += 1,
            ClauseKind::Projection(_) => num_trait_type_constraints += 1,
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
