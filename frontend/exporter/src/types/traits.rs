use crate::prelude::*;

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ImplSource {
    UserDefined(ImplSourceUserDefinedData),
    Param(Binder<TraitRef>, Vec<ImplSource>, BoundConstness),
    Object(ImplSourceObjectData),
    /// For builtin traits such as [core::marker::Sized].
    Builtin(Binder<TraitRef>, Vec<ImplSource>),
    TraitUpcasting(ImplSourceTraitUpcastingData),
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ImplSourceUserDefinedData {
    pub impl_def_id: DefId,
    pub substs: Vec<GenericArg>,
    pub nested: Vec<ImplSource>,
}

#[derive(AdtInto, Copy, Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::BoundConstness, state: S as _s)]
pub enum BoundConstness {
    NotConst,
    ConstIfConst,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ImplSourceObjectData {
    pub upcast_trait_ref: Binder<TraitRef>,
    pub vtable_base: usize,
    pub nested: Vec<ImplSource>,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ImplSourceTraitUpcastingData {
    pub upcast_trait_ref: Binder<TraitRef>,
    pub vtable_vptr_slot: Option<usize>,
    pub nested: Vec<ImplSource>,
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
fn solve_obligation<'tcx, S: BaseState<'tcx>>(
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

fn solve_obligations<'tcx, S: BaseState<'tcx>>(
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
pub fn solve_trait<'tcx, S: BaseState<'tcx>>(
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
        _ => {
            unimplemented!()
        }
    }
}

pub type TraitInfo = ImplSource;

/// Solve the trait obligations for a specific item.
pub fn solve_item_traits<'tcx, S: BaseState<'tcx>>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Vec<ImplSource> {
    let tcx = s.base().tcx;

    let mut trait_infos = Vec::new();

    // Lookup the predicates and iter through them: we want to solve all the
    // trait requirements.
    let predicates = tcx.predicates_of(def_id);
    for (pred, _) in predicates.predicates {
        // SH: We need to apply the substitution. Not sure this is the proper way,
        // but it seems to work so far. My reasoning:
        // - I don't know how to get rid of the Binder, because there is no
        //   Binder::subst method.
        // - However I notice that EarlyBinder is just a wrapper (it doesn't
        //   contain any information) and comes with substitution methods.
        // So I skip the Binder, wrap the value in an EarlyBinder and apply
        // the substitution.
        // Remark: there is also EarlyBinder::subst(...)
        let pred_kind = rustc_middle::ty::EarlyBinder::bind(pred.kind().skip_binder());
        let pred_kind = tcx.subst_and_normalize_erasing_regions(substs, param_env, pred_kind);

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
