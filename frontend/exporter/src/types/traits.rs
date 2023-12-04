use crate::prelude::*;

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub enum ImplSourceKind {
    UserDefined(ImplSourceUserDefinedData),
    Param(Binder<TraitRef>, Vec<ImplSource>, BoundConstness),
    Object(ImplSourceObjectData),
    /// For builtin traits such as [core::marker::Sized].
    Builtin(Binder<TraitRef>, Vec<ImplSource>),
    TraitUpcasting(ImplSourceTraitUpcastingData),
    /// For instance of [core::marker::Sync] for instance
    AutoImpl(ImplSourceAutoImplData),
    /// When using a function pointer as an object implementing `Fn`, `FnMut`, etc.
    FnPointer(ImplSourceFnPointerData),
    Closure(ImplSourceClosureData),
    ///
    Todo(String),
    /// When the resolution failed
    Error(String),
}

/// We extend the impl source information with predicate information, in order
/// to remember which trait obligation was solved (this gives us useful typing
/// information about the impl source).
#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ImplSource {
    pub kind: ImplSourceKind,
    pub trait_ref: TraitRef,
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

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ImplSourceFnPointerData {
    pub fn_ty: Box<Ty>,
    pub nested: Vec<ImplSource>,
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ImplSourceClosureData {
    pub closure_def_id: DefId,
    pub parent_substs: Vec<GenericArg>,
    pub sig: Box<MirPolyFnSig>,
    pub nested: Vec<ImplSource>,
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
        rustc_middle::ty::PredicateKind::ClosureKind(..) => {
            // Ignoring those - TODO: not sure what to do here
            Option::None
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
    // Normalize the trait reference (TODO: we do this because for now
    // [select_trait_candidate] expects the input to be fully normalized).
    let tcx = s.base().tcx;
    let trait_ref = tcx.normalize_erasing_regions(param_env, trait_ref);

    use rustc_trait_selection::traits::ImplSource as RustImplSource;
    use std::result::Result::*;
    let kind = match select_trait_candidate(tcx, param_env, trait_ref) {
        Err(e) => ImplSourceKind::Error(format!(
            "Error ({:?}) when solving trait obligation: {:?}",
            e, trait_ref
        )),
        Ok(kind) => {
            match kind {
                RustImplSource::UserDefined(
                    rustc_trait_selection::traits::ImplSourceUserDefinedData {
                        impl_def_id,
                        substs,
                        nested,
                    },
                ) => ImplSourceKind::UserDefined(ImplSourceUserDefinedData {
                    impl_def_id: impl_def_id.sinto(s),
                    substs: substs.sinto(s),
                    nested: solve_obligations(s, nested),
                }),
                RustImplSource::Param(obligations, constness) => {
                    // We preserve the trait ref, because we will need it to figure out
                    // **which** where clause actually solves this trait obligation.
                    let trait_ref = trait_ref.sinto(s);
                    assert!(obligations.is_empty());
                    let obligations = solve_obligations(s, obligations);
                    let constness = constness.sinto(s);
                    ImplSourceKind::Param(trait_ref, obligations, constness)
                }
                RustImplSource::Object(rustc_trait_selection::traits::ImplSourceObjectData {
                    upcast_trait_ref,
                    vtable_base,
                    nested,
                }) => {
                    ImplSourceKind::Object(ImplSourceObjectData {
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
                    ImplSourceKind::Builtin(trait_ref, solve_obligations(s, nested))
                }
                RustImplSource::TraitUpcasting(
                    rustc_trait_selection::traits::ImplSourceTraitUpcastingData {
                        upcast_trait_ref,
                        vtable_vptr_slot,
                        nested,
                    },
                ) => {
                    ImplSourceKind::TraitUpcasting(ImplSourceTraitUpcastingData {
                        upcast_trait_ref: upcast_trait_ref.sinto(s),
                        // TODO: we probably need to add information for the vtable
                        vtable_vptr_slot,
                        nested: solve_obligations(s, nested),
                    })
                }
                RustImplSource::AutoImpl(
                    rustc_trait_selection::traits::ImplSourceAutoImplData {
                        trait_def_id,
                        nested,
                    },
                ) => ImplSourceKind::AutoImpl(ImplSourceAutoImplData {
                    trait_def_id: trait_def_id.sinto(s),
                    nested: nested.iter().map(|x| format!("{:?}", x)).collect(),
                }),
                // Happens when we use a function pointer as an object implementing
                // a trait like `FnMut`
                RustImplSource::FnPointer(
                    rustc_trait_selection::traits::ImplSourceFnPointerData { fn_ty, nested },
                ) => ImplSourceKind::FnPointer(ImplSourceFnPointerData {
                    fn_ty: fn_ty.sinto(s),
                    nested: solve_obligations(s, nested),
                }),
                RustImplSource::Closure(rustc_trait_selection::traits::ImplSourceClosureData {
                    closure_def_id,
                    substs,
                    nested,
                }) => {
                    let substs = substs.as_closure();
                    let parent_substs = substs.parent_substs().sinto(s);
                    let sig = Box::new(substs.sig().sinto(s));
                    ImplSourceKind::Closure(ImplSourceClosureData {
                        closure_def_id: closure_def_id.sinto(s),
                        parent_substs,
                        sig,
                        nested: solve_obligations(s, nested),
                    })
                }
                impl_source => ImplSourceKind::Todo(format!("impl source: {:?}", impl_source)),
            }
        }
    };

    // Solve the trait ref
    let trait_ref = {
        let tr = trait_ref.sinto(s);
        assert!(trait_ref.bound_vars().is_empty());
        TraitRef {
            def_id: tr.value.def_id,
            generic_args: tr.value.generic_args,
        }
    };
    ImplSource { kind, trait_ref }
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub struct TraitInfo {
    pub impl_source: ImplSource,
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

    // Get the full trait information
    get_trait_info_for_trait_ref(s, ref_def_id, param_env, tr_ref)
}

/// Retrieve the trait information, typically for a function call.
/// [ref_def_id]: id of the method being called, the global being used, etc.
pub fn get_trait_info_for_trait_ref<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    _ref_def_id: rustc_hir::def_id::DefId,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> (Vec<GenericArg>, TraitInfo) {
    let mut impl_source = solve_trait(s, param_env, trait_ref);

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
        let src_id = src_id.rust_def_id.unwrap();
        let params_info = get_params_info(s, src_id);
        let num_trait_generics = params_info.num_generic_params;
        let all_generics = x.clone();
        (all_generics, x.split_off(num_trait_generics))
    };

    let (all_generics, truncated_generics) = match &mut impl_source.kind {
        ImplSourceKind::UserDefined(data) => update_generics(&data.impl_def_id, &mut data.substs),
        ImplSourceKind::Param(trait_ref, _, _) => {
            update_generics(&trait_ref.value.def_id, &mut trait_ref.value.generic_args)
        }
        ImplSourceKind::Error(_) | ImplSourceKind::Todo(_) => {
            // We do something similar to the param case
            let mut trait_ref = trait_ref.sinto(s);
            update_generics(&trait_ref.value.def_id, &mut trait_ref.value.generic_args)
        }
        ImplSourceKind::Object(_data) => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl source:\n{:?}",
                trait_ref,
                impl_source
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
        ImplSourceKind::Builtin(_trait_ref, _) => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl source:\n{:?}",
                trait_ref,
                impl_source
            )
            // update_generics(&mut trait_ref.value.generic_args)
        }
        ImplSourceKind::TraitUpcasting(_data) => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl source:\n{:?}",
                trait_ref,
                impl_source
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
        ImplSourceKind::AutoImpl(_data) => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl source:\n{:?}",
                trait_ref,
                impl_source
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
        ImplSourceKind::FnPointer(_data) => {
            // TODO: not sure
            todo!(
                "\n- trait_ref:\n{:?}\n\n- impl source:\n{:?}",
                trait_ref,
                impl_source
            )
            // update_generics(&mut data.upcast_trait_ref.value.generic_args)
        }
        ImplSourceKind::Closure(_) => {
            // We don't need to truncate the generics (there shouldn't be any)
            let trait_ref = trait_ref.sinto(s);
            (
                trait_ref.value.generic_args.clone(),
                trait_ref.value.generic_args,
            )
        }
    };

    let info = TraitInfo {
        impl_source,
        all_generics,
    };
    (truncated_generics, info)
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

/// Solve the trait obligations for a specific item use (for example, a method
/// call, an ADT, etc.).
///
/// [predicates]: optional predicates, in case we want to solve custom predicates
/// (instead of the ones returned by [TyCtxt::predicates_defined_on].
pub fn solve_item_traits<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
    predicates: Option<rustc_middle::ty::GenericPredicates<'tcx>>,
) -> Vec<ImplSource> {
    let tcx = s.base().tcx;

    let mut trait_infos = Vec::new();

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
            let trait_info = if trait_ref.has_escaping_bound_vars() {
                // Error
                let kind =
                    ImplSourceKind::Error(format!("{:?} has escaping bound vars", trait_ref));
                let trait_ref = {
                    let tr = trait_ref.sinto(s);
                    TraitRef {
                        def_id: tr.def_id,
                        generic_args: tr.generic_args,
                    }
                };

                ImplSource { kind, trait_ref }
            } else {
                // Ok
                let trait_ref = rustc_middle::ty::Binder::dummy(trait_pred.trait_ref);
                solve_trait(s, param_env, trait_ref)
            };

            trait_infos.push(trait_info);
        }
    }
    trait_infos
}
