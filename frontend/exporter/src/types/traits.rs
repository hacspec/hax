use crate::prelude::*;

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub enum ImplSource {
    UserDefined(ImplSourceUserDefinedData),
    Param(Binder<TraitRef>, Vec<ImplSource>, BoundConstness),
    Object(ImplSourceObjectData),
    /// For builtin traits such as [core::marker::Sized].
    Builtin(Binder<TraitRef>, Vec<ImplSource>),
    TraitUpcasting(ImplSourceTraitUpcastingData),
    /// For instance of [core::marker::Sync] for instance
    AutoImpl(ImplSourceAutoImplData),
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ImplSourceUserDefinedData {
    pub impl_def_id: DefId,
    pub substs: Vec<GenericArg>,
    pub nested: Vec<ImplSource>,
}

#[derive(
    AdtInto,
    Copy,
    Clone,
    Debug,
    Serialize,
    Deserialize,
    JsonSchema,
    Hash,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::BoundConstness, state: S as _s)]
pub enum BoundConstness {
    NotConst,
    ConstIfConst,
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ImplSourceObjectData {
    pub upcast_trait_ref: Binder<TraitRef>,
    pub vtable_base: usize,
    pub nested: Vec<ImplSource>,
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ImplSourceTraitUpcastingData {
    pub upcast_trait_ref: Binder<TraitRef>,
    pub vtable_vptr_slot: Option<usize>,
    pub nested: Vec<ImplSource>,
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ImplSourceAutoImplData {
    pub trait_def_id: DefId,
    /// Solving the nested obligations sometimes loops.
    /// For instance, if you query a candidate for [core::marker::Syn<u8>],
    /// it returns the an auto impl with the nested proof obligation that
    /// we have [core::marker::Syn<u8>].
    /// We could detect those cases, but as we don't use the auto impls for
    /// now, we prefer to ignore the nested obligations.
    /// TODO: maybe an issue with using [TyCtxt::predicates_of] instead of
    /// [TyCtxt::predicates_defined_on]?
    pub nested: Vec<String>,
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
    let preds = tcx.predicates_defined_on(def_id).sinto(s);
    for (pred, _) in preds.predicates {
        match &pred.value {
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

/// Adapted from [rustc_trait_selection::traits::SelectionContext::select]:
/// we want to preserve the nested obligations to resolve them afterwards.
///
/// Example:
/// ========
/// ```text
/// struct Wrapper<T> {
///    x: T,
/// }
///
/// impl<T: ToU64> ToU64 for Wrapper<T> {
///     fn to_u64(self) -> u64 {
///         self.x.to_u64()
///     }
/// }
///
/// fn h(x: Wrapper<u64>) -> u64 {
///     x.to_u64()
/// }
/// ```
///
/// When resolving the trait for `x.to_u64()` in `h`, we get that it uses the
/// implementation for `Wrapper`. But we also need to know the obligation generated
/// for `Wrapper` (in this case: `u64 : ToU64`) and resolve it.
pub fn select_trait_candidate<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> Result<
    rustc_trait_selection::traits::Selection<'tcx>,
    rustc_middle::traits::CodegenObligationError,
> {
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_middle::traits::CodegenObligationError;
    use rustc_trait_selection::traits::{
        Obligation, ObligationCause, SelectionContext, Unimplemented,
    };

    // We expect the input to be fully normalized.
    debug_assert_eq!(
        trait_ref,
        tcx.normalize_erasing_regions(param_env, trait_ref)
    );

    // Do the initial selection for the obligation. This yields the
    // shallow result we are looking for -- that is, what specific impl.
    let infcx = tcx.infer_ctxt().ignoring_regions().build();
    let mut selcx = SelectionContext::new(&infcx);

    let obligation_cause = ObligationCause::dummy();
    let obligation = Obligation::new(tcx, obligation_cause, param_env, trait_ref);

    match selcx.select(&obligation) {
        Ok(Some(selection)) => {
            let selection = infcx.resolve_vars_if_possible(selection);
            Ok(selection)
        }
        Ok(None) => Err(CodegenObligationError::Ambiguity),
        Err(Unimplemented) =>
        // The trait is not implemented
        {
            Err(CodegenObligationError::Unimplemented)
        }
        Err(e) => {
            panic!(
                "Encountered error `{:?}` selecting `{:?}` during codegen",
                e, trait_ref
            )
        }
    }
}

/// Solve an obligation.
///
/// Note that we skip some obligations (for instance, obligations stating that a
/// lifetime outlives another lifetime). The reason is that, provided those
/// obligations are satisfiable (this is done at type checking time) we don't
/// need to return any information about this obligation, and in particular we
/// don't need a witness (contrary to the traits).
fn solve_obligation<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    obligation: rustc_trait_selection::traits::Obligation<'tcx, rustc_middle::ty::Predicate<'tcx>>,
) -> Option<ImplSource> {
    let predicate = obligation.predicate.kind();
    // For now we assume the predicate is necessarily a trait predicate.
    // We thus convert it to that: this implies diving into the predicate
    // to retrieve the proper information.
    match predicate.skip_binder() {
        rustc_middle::ty::PredicateKind::Clause(clause) => {
            use rustc_middle::ty::Clause;
            match clause {
                Clause::Trait(trait_pred) => {
                    let trait_ref = trait_pred.trait_ref;

                    // Create the trait obligation by using the above binder
                    let trait_ref =
                        rustc_middle::ty::Binder::bind_with_vars(trait_ref, predicate.bound_vars());

                    // Solve
                    Option::Some(solve_trait(s, obligation.param_env, trait_ref))
                }
                Clause::RegionOutlives(..)
                | Clause::TypeOutlives(..)
                | Clause::ConstArgHasType(..)
                | Clause::Projection(..) => Option::None,
            }
        }
        x => {
            // SH: We probably just need to ignore those, like for the Clauses,
            // but I'm not familiar enough with the meaning of those predicates
            // to actually do anything about them yet.
            unreachable!("Unexpected predicate kind: {:?}", x)
        }
    }
}

fn solve_obligations<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    obligations: Vec<
        rustc_trait_selection::traits::Obligation<'tcx, rustc_middle::ty::Predicate<'tcx>>,
    >,
) -> Vec<ImplSource> {
    obligations
        .into_iter()
        .filter_map(|o| solve_obligation(s, o))
        .collect()
}

/// Compute the full trait information (recursively solve the nested obligations).
pub fn solve_trait<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> ImplSource {
    let tcx = s.base().tcx;

    use rustc_trait_selection::traits::ImplSource as RustImplSource;
    match select_trait_candidate(tcx, param_env, trait_ref).unwrap() {
        RustImplSource::UserDefined(rustc_trait_selection::traits::ImplSourceUserDefinedData {
            impl_def_id,
            substs,
            nested,
        }) => ImplSource::UserDefined(ImplSourceUserDefinedData {
            impl_def_id: impl_def_id.sinto(s),
            substs: substs.sinto(s),
            nested: solve_obligations(s, nested),
        }),
        RustImplSource::Param(obligations, constness) => {
            // We preserve the trait ref, because we will need it to figure out
            // **which** where clause actually solves this trait obligation.
            let trait_ref = trait_ref.sinto(s);
            let obligations = solve_obligations(s, obligations);
            let constness = constness.sinto(s);
            ImplSource::Param(trait_ref, obligations, constness)
        }
        RustImplSource::Object(rustc_trait_selection::traits::ImplSourceObjectData {
            upcast_trait_ref,
            vtable_base,
            nested,
        }) => {
            ImplSource::Object(ImplSourceObjectData {
                upcast_trait_ref: upcast_trait_ref.sinto(s),
                // TODO: we probably need to add information for the vtable
                vtable_base,
                nested: solve_obligations(s, nested),
            })
        }
        RustImplSource::Builtin(rustc_trait_selection::traits::ImplSourceBuiltinData {
            nested,
        }) => {
            // Same as for the Param case: we preserve the trait ref
            let trait_ref = trait_ref.sinto(s);
            ImplSource::Builtin(trait_ref, solve_obligations(s, nested))
        }
        RustImplSource::TraitUpcasting(
            rustc_trait_selection::traits::ImplSourceTraitUpcastingData {
                upcast_trait_ref,
                vtable_vptr_slot,
                nested,
            },
        ) => {
            ImplSource::TraitUpcasting(ImplSourceTraitUpcastingData {
                upcast_trait_ref: upcast_trait_ref.sinto(s),
                // TODO: we probably need to add information for the vtable
                vtable_vptr_slot,
                nested: solve_obligations(s, nested),
            })
        }
        RustImplSource::AutoImpl(rustc_trait_selection::traits::ImplSourceAutoImplData {
            trait_def_id,
            nested,
        }) => ImplSource::AutoImpl(ImplSourceAutoImplData {
            trait_def_id: trait_def_id.sinto(s),
            nested: nested.iter().map(|x| format!("{:?}", x)).collect(),
        }),
        impl_source => {
            unimplemented!("impl source: {:?}", impl_source)
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitInfo {
    pub impl_source: ImplSource,
    pub params_info: ParamsInfo,
    /// All the generics (from before truncating them - see the documentation
    /// for [ParamsInfo]). We store this information mostly for debugging purposes.
    pub all_generics: Vec<GenericArg>,
}

/// Retrieve the trait information, typically for a function call.
/// [ref_def_id]: id of the method being called, the global being used, etc.
pub fn get_trait_info<'tcx, S: BaseState<'tcx> + HasOwnerId>(
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

    // Check if we can resolve - not sure if really necessary
    let _ = tcx.codegen_select_candidate((param_env, tr_ref)).unwrap();

    // Get the full trait information
    get_trait_info_for_trait_ref(s, ref_def_id, param_env, tr_ref)
}

/// Retrieve the trait information, typically for a function call.
/// [ref_def_id]: id of the method being called, the global being used, etc.
pub fn get_trait_info_for_trait_ref<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    ref_def_id: rustc_hir::def_id::DefId,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> (Vec<GenericArg>, TraitInfo) {
    let mut impl_source = solve_trait(s, param_env, trait_ref);

    // We need to remove the arguments which are for the method: we keep the
    // arguments which are specific to the trait instance (see the comments
    // in [ParamsInfo]).
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
    let params_info = get_parent_params_info(s, ref_def_id).unwrap();

    let update_generics = |x: &mut Vec<GenericArg>| {
        let original = x.clone();
        *x = x[0..params_info.num_generic_params].to_vec();
        (original, x.clone())
    };

    // SH: For some reason we don't need to filter the generics everywhere.
    // I don't understand the logic.
    let (all_generics, truncated_generics) = match &mut impl_source {
        ImplSource::UserDefined(data) => {
            // We don't need to do anything here
            (data.substs.clone(), data.substs.clone())
        }
        ImplSource::Param(trait_ref, _, _) => {
            // We need to filter here
            update_generics(&mut trait_ref.value.generic_args)
        }
        ImplSource::Object(_data) => {
            // TODO: not sure
            todo!(
                "- trait_ref:\n{:?}\n- params info:\n{:?}\n- impl source:{:?}",
                trait_ref,
                params_info,
                impl_source
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
        ImplSource::Builtin(_trait_ref, _) => {
            // TODO: not sure
            todo!(
                "- trait_ref:\n{:?}\n- params info:\n{:?}\n- impl source:{:?}",
                trait_ref,
                params_info,
                impl_source
            )
            // update_generics(&mut trait_ref.value.generic_args)
        }
        ImplSource::TraitUpcasting(_data) => {
            // TODO: not sure
            todo!(
                "- trait_ref:\n{:?}\n- params info:\n{:?}\n- impl source:{:?}",
                trait_ref,
                params_info,
                impl_source
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
        ImplSource::AutoImpl(_data) => {
            // TODO: not sure
            todo!(
                "- trait_ref:\n{:?}\n- params info:\n{:?}\n- impl source:{:?}",
                trait_ref,
                params_info,
                impl_source
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
    };

    let info = TraitInfo {
        impl_source,
        params_info,
        all_generics,
    };
    (truncated_generics, info)
}

/// Small helper.
///
/// Introducing this to make sure all binders are handled in a consistent manner.
pub(crate) fn subst_binder<'tcx, T>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    param_substs: rustc_middle::ty::SubstsRef<'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    value: rustc_middle::ty::Binder<'tcx, T>,
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
    tcx.subst_and_normalize_erasing_regions(param_substs, param_env, value)
}

/// Solve the trait obligations for a specific item use (for example, a method
/// call, an ADT, etc.).
pub fn solve_item_traits<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Vec<ImplSource> {
    let tcx = s.base().tcx;

    let mut trait_infos = Vec::new();

    // Lookup the predicates and iter through them: we want to solve all the
    // trait requirements.
    // TODO: should we use predicates_defined_on?
    let predicates = tcx.predicates_of(def_id);
    for (pred, _) in predicates.predicates {
        // Apply the substitution
        let pred_kind = subst_binder(tcx, substs, param_env, pred.kind());

        // Just explore the trait predicates
        use rustc_middle::ty::{Clause, PredicateKind};
        if let PredicateKind::Clause(Clause::Trait(trait_pred)) = pred_kind {
            // SH: We also need to introduce a binder here. I'm not sure what we
            // whould bind this with: the variables to bind with are those
            // given by the definition we are exploring, and they should already
            // be in the param environment. So I just wrap in a dummy binder
            // (this also seems to work so far).
            let trait_ref = rustc_middle::ty::Binder::dummy(trait_pred.trait_ref);
            trait_infos.push(solve_trait(s, param_env, trait_ref));
        }
    }
    trait_infos
}
