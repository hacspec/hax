use crate::prelude::*;
use crate::rustc_middle::query::Key;

/*
pub enum ImplSource {
    UserDefined(ImplSourceUserDefinedData),
    Param(Vec<ImplSource>, BoundConstness),
    Object(ImplSourceObjectData),
    Builtin(Vec<ImplSource>),
    TraitUpcasting(ImplSourceTraitUpcastingData),
}
*/

// Small trick: we need to instantiate the type parameter, but can't do it
// in the AdtInto macro, so we define a type alias.
type UnitImplSource<'tcx> = rustc_middle::traits::ImplSource<'tcx, ()>;

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: UnitImplSource<'tcx>, state: S as s)]
pub enum ImplSource {
    /*    UserDefined(ImplSourceUserDefinedData<N>),
    AutoImpl(ImplSourceAutoImplData),
    Param(Vec<N>, BoundConstness),
    Object(ImplSourceObjectData<N>),
    Builtin(ImplSourceBuiltinData<N>),
    TraitUpcasting(ImplSourceTraitUpcastingData<N>),
    Closure(ImplSourceClosureData<N>),
    FnPointer(ImplSourceFnPointerData<N>),
    Generator(ImplSourceGeneratorData<N>),
    Future(ImplSourceFutureData<N>),
    TraitAlias(ImplSourceTraitAliasData<N>),
    ConstDestruct(ImplSourceConstDestructData<N>), */
    //    UserDefined(String),
    //    Param(Vec<()>, String),
    //    Closure(String),
    //    FnPointer(String),
    #[todo]
    Todo(String),
}

/*impl<'tcx, S: BaseState<'tcx>, N> SInto<S, ImplSource<N>>
    for rustc_middle::traits::ImplSource<'tcx, N>
{
    fn sinto(self: &rustc_middle::traits::ImplSource<'tcx, N>, s: &S) -> ImplSource<N> {
        let ctx = rustc_hir_analysis::collect::ItemCtxt::new(s.base().tcx, s.owner_id().def_id);
        ctx.to_ty(self).sinto(s)
    }
}*/

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_trait_selection::traits::ObligationCause<'tcx>, state: S as s)]
pub struct ObligationCause {
    pub span: Span,
    #[map(x.to_def_id().sinto(s))]
    pub body_id: DefId,
    //code: InternedObligationCauseCode,
}

pub type ParamEnv = Vec<Predicate>;

impl<'tcx, S: BaseState<'tcx>> SInto<S, ParamEnv> for rustc_middle::ty::ParamEnv<'tcx> {
    fn sinto(&self, s: &S) -> ParamEnv {
        self.caller_bounds().sinto(s)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Obligation<T> {
    pub cause: ObligationCause,
    pub param_env: ParamEnv,
    pub predicate: T,
    pub recursion_depth: usize,
}

impl<'tcx, S: BaseState<'tcx>, T1, T2> SInto<S, Obligation<T2>>
    for rustc_trait_selection::traits::Obligation<'tcx, T1>
where
    T1: SInto<S, T2>,
{
    fn sinto(&self, s: &S) -> Obligation<T2> {
        let cause = self.cause.sinto(s);
        let param_env = self.param_env.sinto(s);
        let predicate = self.predicate.sinto(s);
        let recursion_depth = self.recursion_depth;
        Obligation {
            cause,
            param_env,
            predicate,
            recursion_depth,
        }
    }
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

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitInfo {
    pub impl_source: ImplSource,
    pub selection: String,
}
