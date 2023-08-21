use crate::prelude::*;

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ImplSource {
    UserDefined(ImplSourceUserDefinedData),
    Param(Vec<ImplSource>, BoundConstness),
    Object(ImplSourceObjectData),
    Builtin(Vec<ImplSource>),
    TraitUpcasting(ImplSourceTraitUpcastingData),
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ImplSourceUserDefinedData {
    pub impl_def_id: DefId,
    pub substs: Vec<GenericArg>,
    pub nested: Vec<ImplSource>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
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
    (param_env, trait_ref): (
        rustc_middle::ty::ParamEnv<'tcx>,
        rustc_middle::ty::PolyTraitRef<'tcx>,
    ),
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
        Ok(Some(selection)) => Ok(selection),
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

/// Compute the full trait information (recursively solve the nested obligations).
pub fn get_trait_info<'tcx, S: BaseState<'tcx>>(
    s: &S,
    (param_env, trait_ref): (
        rustc_middle::ty::ParamEnv<'tcx>,
        rustc_middle::ty::PolyTraitRef<'tcx>,
    ),
) -> ImplSource {
    let tcx = s.base().tcx;

    use rustc_trait_selection::traits::ImplSource as RustImplSource;
    match select_trait_candidate(tcx, (param_env, trait_ref)).unwrap() {
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
            let obligations = solve_obligations(s, obligations);
            let constness = constness.sinto(s);
            ImplSource::Param(obligations, constness)
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
        }) => ImplSource::Builtin(solve_obligations(s, nested)),
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

fn solve_obligation<'tcx, S: BaseState<'tcx>>(
    s: &S,
    obligation: rustc_trait_selection::traits::Obligation<'tcx, rustc_middle::ty::Predicate<'tcx>>,
) -> ImplSource {
    let predicate = obligation.predicate.kind();
    // For now we assume the predicate is necessarily a trait predicate.
    // We thus convert it to that: this implies diving into the predicate
    // to retrieve the proper information.
    match predicate.skip_binder() {
        rustc_middle::ty::PredicateKind::Clause(clause) => {
            match clause {
                rustc_middle::ty::Clause::Trait(trait_pred) => {
                    let trait_ref = trait_pred.trait_ref;

                    // Create the trait obligation by using the above binder
                    let trait_ref =
                        rustc_middle::ty::Binder::bind_with_vars(trait_ref, predicate.bound_vars());

                    // Solve
                    get_trait_info(s, (obligation.param_env, trait_ref))
                }
                x => {
                    // Unexpected.
                    // Actually, we probably need to just ignore those.
                    unreachable!("Unexpected clause kind: {:?}", x)
                }
            }
        }
        x => {
            // Unexpected
            // Actually, we probably need to just ignore those.
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
        .map(|o| solve_obligation(s, o))
        .collect()
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitInfo {
    pub selection: String,
}
