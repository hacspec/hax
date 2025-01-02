//! Trait resolution: given a trait reference, we track which local clause caused it to be true.
//! This module is independent from the rest of hax, in particular it doesn't use its
//! state-tracking machinery.

use itertools::Itertools;
use std::collections::{hash_map::Entry, HashMap};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::traits::CodegenObligationError;
use rustc_middle::ty::*;
use rustc_trait_selection::traits::ImplSource;

use crate::{self_predicate, traits::utils::erase_and_norm};

use super::utils::{implied_predicates, required_predicates};

#[derive(Debug, Clone)]
pub enum PathChunk<'tcx> {
    AssocItem {
        item: AssocItem,
        /// The arguments provided to the item (for GATs).
        generic_args: &'tcx [GenericArg<'tcx>],
        /// The impl exprs that must be satisfied to apply the given arguments to the item. E.g.
        /// `T: Clone` in the following example:
        /// ```ignore
        /// trait Foo {
        ///     type Type<T: Clone>: Debug;
        /// }
        /// ```
        impl_exprs: Vec<ImplExpr<'tcx>>,
        /// The implemented predicate.
        predicate: PolyTraitPredicate<'tcx>,
        /// The index of this predicate in the list returned by `implied_predicates`.
        index: usize,
    },
    Parent {
        /// The implemented predicate.
        predicate: PolyTraitPredicate<'tcx>,
        /// The index of this predicate in the list returned by `implied_predicates`.
        index: usize,
    },
}
pub type Path<'tcx> = Vec<PathChunk<'tcx>>;

#[derive(Debug, Clone)]
pub enum ImplExprAtom<'tcx> {
    /// A concrete `impl Trait for Type {}` item.
    Concrete {
        def_id: DefId,
        generics: GenericArgsRef<'tcx>,
    },
    /// A context-bound clause like `where T: Trait`.
    LocalBound {
        predicate: Predicate<'tcx>,
        /// The nth (non-self) predicate found for this item. We use predicates from
        /// `required_predicates` starting from the parentmost item.
        index: usize,
        r#trait: PolyTraitRef<'tcx>,
        path: Path<'tcx>,
    },
    /// The automatic clause `Self: Trait` present inside a `impl Trait for Type {}` item.
    SelfImpl {
        r#trait: PolyTraitRef<'tcx>,
        path: Path<'tcx>,
    },
    /// `dyn Trait` is a wrapped value with a virtual table for trait
    /// `Trait`.  In other words, a value `dyn Trait` is a dependent
    /// triple that gathers a type τ, a value of type τ and an
    /// instance of type `Trait`.
    /// `dyn Trait` implements `Trait` using a built-in implementation; this refers to that
    /// built-in implementation.
    Dyn,
    /// A built-in trait whose implementation is computed by the compiler, such as `Sync`.
    Builtin { r#trait: PolyTraitRef<'tcx> },
    /// An error happened while resolving traits.
    Error(String),
}

#[derive(Clone, Debug)]
pub struct ImplExpr<'tcx> {
    /// The trait this is an impl for.
    pub r#trait: PolyTraitRef<'tcx>,
    /// The kind of implemention of the root of the tree.
    pub r#impl: ImplExprAtom<'tcx>,
    /// A list of `ImplExpr`s required to fully specify the trait references in `impl`.
    pub args: Vec<Self>,
}

/// Items have various predicates in scope. `path_to` uses them as a starting point for trait
/// resolution. This tracks where each of them comes from.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum BoundPredicateOrigin {
    /// The `Self: Trait` predicate implicitly present within trait declarations (note: we
    /// don't add it for trait implementations, should we?).
    SelfPred,
    /// The nth (non-self) predicate found for this item. We use predicates from
    /// `required_predicates` starting from the parentmost item.
    Item(usize),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedTraitPred<'tcx> {
    pub origin: BoundPredicateOrigin,
    pub clause: PolyTraitPredicate<'tcx>,
}

/// The predicates to use as a starting point for resolving trait references within this item. This
/// includes the "self" predicate if applicable and the `required_predicates` of this item and all
/// its parents, numbered starting from the parents.
fn initial_search_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
) -> Vec<AnnotatedTraitPred<'tcx>> {
    fn acc_predicates<'tcx>(
        tcx: TyCtxt<'tcx>,
        def_id: rustc_span::def_id::DefId,
        predicates: &mut Vec<AnnotatedTraitPred<'tcx>>,
        pred_id: &mut usize,
    ) {
        let next_item_origin = |pred_id: &mut usize| {
            let origin = BoundPredicateOrigin::Item(*pred_id);
            *pred_id += 1;
            origin
        };
        use DefKind::*;
        match tcx.def_kind(def_id) {
            // These inherit some predicates from their parent.
            AssocTy | AssocFn | AssocConst | Closure | Ctor(..) | Variant => {
                let parent = tcx.parent(def_id);
                acc_predicates(tcx, parent, predicates, pred_id);
            }
            Trait => {
                let self_pred = self_predicate(tcx, def_id).upcast(tcx);
                predicates.push(AnnotatedTraitPred {
                    origin: BoundPredicateOrigin::SelfPred,
                    clause: self_pred,
                })
            }
            _ => {}
        }
        predicates.extend(
            required_predicates(tcx, def_id)
                .predicates
                .iter()
                .map(|(clause, _span)| *clause)
                .filter_map(|clause| {
                    clause.as_trait_clause().map(|clause| AnnotatedTraitPred {
                        origin: next_item_origin(pred_id),
                        clause,
                    })
                }),
        );
    }

    let mut predicates = vec![];
    acc_predicates(tcx, def_id, &mut predicates, &mut 0);
    predicates
}

#[tracing::instrument(level = "trace", skip(tcx))]
fn parents_trait_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    pred: PolyTraitPredicate<'tcx>,
) -> Vec<PolyTraitPredicate<'tcx>> {
    let self_trait_ref = pred.to_poly_trait_ref();
    implied_predicates(tcx, pred.def_id())
        .predicates
        .iter()
        .map(|(clause, _span)| *clause)
        // Substitute with the `self` args so that the clause makes sense in the
        // outside context.
        .map(|clause| clause.instantiate_supertrait(tcx, self_trait_ref))
        .filter_map(|pred| pred.as_trait_clause())
        .collect()
}

/// A candidate projects `self` along a path reaching some predicate. A candidate is
/// selected when its predicate is the one expected, aka `target`.
#[derive(Debug, Clone)]
struct Candidate<'tcx> {
    path: Path<'tcx>,
    pred: PolyTraitPredicate<'tcx>,
    origin: AnnotatedTraitPred<'tcx>,
}

/// Stores a set of predicates along with where they came from.
pub struct PredicateSearcher<'tcx> {
    tcx: TyCtxt<'tcx>,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    /// Local clauses available in the current context.
    candidates: HashMap<PolyTraitPredicate<'tcx>, Candidate<'tcx>>,
}

impl<'tcx> PredicateSearcher<'tcx> {
    /// Initialize the elaborator with the predicates accessible within this item.
    pub fn new_for_owner(tcx: TyCtxt<'tcx>, owner_id: DefId) -> Self {
        let mut out = Self {
            tcx,
            param_env: tcx.param_env(owner_id).with_reveal_all_normalized(tcx),
            candidates: Default::default(),
        };
        out.extend(
            initial_search_predicates(tcx, owner_id)
                .into_iter()
                .map(|clause| Candidate {
                    path: vec![],
                    pred: clause.clause,
                    origin: clause,
                }),
        );
        out
    }

    /// Insert new candidates and all their parent predicates. This deduplicates predicates
    /// to avoid divergence.
    fn extend(&mut self, candidates: impl IntoIterator<Item = Candidate<'tcx>>) {
        let tcx = self.tcx;
        // Filter out duplicated candidates.
        let mut new_candidates = Vec::new();
        for mut candidate in candidates {
            // Normalize and erase all lifetimes.
            candidate.pred = erase_and_norm(tcx, self.param_env, candidate.pred);
            if let Entry::Vacant(entry) = self.candidates.entry(candidate.pred) {
                entry.insert(candidate.clone());
                new_candidates.push(candidate);
            }
        }
        if !new_candidates.is_empty() {
            self.extend_parents(new_candidates);
        }
    }

    /// Add the parents of these candidates. This is a separate function to avoid
    /// polymorphic recursion due to the closures capturing the type parameters of this
    /// function.
    fn extend_parents(&mut self, new_candidates: Vec<Candidate<'tcx>>) {
        let tcx = self.tcx;
        // Then recursively add their parents. This way ensures a breadth-first order,
        // which means we select the shortest path when looking up predicates.
        self.extend(new_candidates.into_iter().flat_map(|candidate| {
            parents_trait_predicates(tcx, candidate.pred)
                .into_iter()
                .enumerate()
                .map(move |(index, parent_pred)| {
                    let mut parent_candidate = Candidate {
                        pred: parent_pred,
                        path: candidate.path.clone(),
                        origin: candidate.origin,
                    };
                    parent_candidate.path.push(PathChunk::Parent {
                        predicate: parent_pred,
                        index,
                    });
                    parent_candidate
                })
        }));
    }

    /// If the type is a trait associated type, we add any relevant bounds to our context.
    fn add_associated_type_refs(
        &mut self,
        ty: Binder<'tcx, Ty<'tcx>>,
        // Call back into hax-related code to display a nice warning.
        warn: &impl Fn(&str),
    ) -> Result<(), String> {
        let tcx = self.tcx;
        // Note: We skip a binder but rebind it just after.
        let TyKind::Alias(AliasTyKind::Projection, alias_ty) = ty.skip_binder().kind() else {
            return Ok(());
        };
        let (trait_ref, item_args) = alias_ty.trait_ref_and_own_args(tcx);
        let trait_ref = ty.rebind(trait_ref).upcast(tcx);

        // The predicate we're looking for is is `<T as Trait>::Type: OtherTrait`. We look up `T as
        // Trait` in the current context and add all the bounds on `Trait::Type` to our context.
        let Some(trait_candidate) = self.resolve_local(trait_ref, warn)? else {
            return Ok(());
        };

        // The bounds that hold on the associated type.
        let item_bounds = implied_predicates(tcx, alias_ty.def_id)
            .predicates
            .iter()
            .map(|(clause, _span)| *clause)
            .filter_map(|pred| pred.as_trait_clause())
            // Substitute the item generics
            .map(|pred| EarlyBinder::bind(pred).instantiate(tcx, alias_ty.args))
            .enumerate();

        // Resolve predicates required to mention the item.
        let nested_impl_exprs =
            self.resolve_item_predicates(alias_ty.def_id, alias_ty.args, warn)?;

        // Add all the bounds on the corresponding associated item.
        self.extend(item_bounds.map(|(index, pred)| {
            let mut candidate = Candidate {
                path: trait_candidate.path.clone(),
                pred,
                origin: trait_candidate.origin,
            };
            candidate.path.push(PathChunk::AssocItem {
                item: tcx.associated_item(alias_ty.def_id),
                generic_args: item_args,
                impl_exprs: nested_impl_exprs.clone(),
                predicate: pred,
                index,
            });
            candidate
        }));

        Ok(())
    }

    /// Resolve a local clause by looking it up in this set. If the predicate applies to an
    /// associated type, we add the relevant implied associated type bounds to the set as well.
    fn resolve_local(
        &mut self,
        target: PolyTraitPredicate<'tcx>,
        // Call back into hax-related code to display a nice warning.
        warn: &impl Fn(&str),
    ) -> Result<Option<Candidate<'tcx>>, String> {
        tracing::trace!("Looking for {target:?}");

        // Look up the predicate
        let ret = self.candidates.get(&target).cloned();
        if ret.is_some() {
            return Ok(ret);
        }

        // Add clauses related to associated type in the `Self` type of the predicate.
        self.add_associated_type_refs(target.self_ty(), warn)?;

        let ret = self.candidates.get(&target).cloned();
        if ret.is_none() {
            tracing::trace!(
                "Couldn't find {target:?} in: [\n{}]",
                self.candidates
                    .iter()
                    .map(|(_, c)| format!("  - {:?}\n", c.pred))
                    .join("")
            );
        }
        Ok(ret)
    }

    /// Resolve the given trait reference in the local context.
    #[tracing::instrument(level = "trace", skip(self, warn))]
    pub fn resolve(
        &mut self,
        tref: &PolyTraitRef<'tcx>,
        // Call back into hax-related code to display a nice warning.
        warn: &impl Fn(&str),
    ) -> Result<ImplExpr<'tcx>, String> {
        use rustc_trait_selection::traits::{
            BuiltinImplSource, ImplSource, ImplSourceUserDefinedData,
        };

        let erased_tref = erase_and_norm(self.tcx, self.param_env, *tref);

        let tcx = self.tcx;
        let impl_source = shallow_resolve_trait_ref(tcx, self.param_env, erased_tref);
        let nested;
        let atom = match impl_source {
            Ok(ImplSource::UserDefined(ImplSourceUserDefinedData {
                impl_def_id,
                args: generics,
                ..
            })) => {
                // Resolve the predicates required by the impl.
                nested = self.resolve_item_predicates(impl_def_id, generics, warn)?;
                ImplExprAtom::Concrete {
                    def_id: impl_def_id,
                    generics,
                }
            }
            Ok(ImplSource::Param(_)) => {
                // Mentioning a local clause requires no extra predicates to hold.
                nested = vec![];
                match self.resolve_local(erased_tref.upcast(self.tcx), warn)? {
                    Some(candidate) => {
                        let path = candidate.path;
                        let r#trait = candidate.origin.clause.to_poly_trait_ref();
                        match candidate.origin.origin {
                            BoundPredicateOrigin::SelfPred => {
                                ImplExprAtom::SelfImpl { r#trait, path }
                            }
                            BoundPredicateOrigin::Item(index) => ImplExprAtom::LocalBound {
                                predicate: candidate.origin.clause.upcast(tcx),
                                index,
                                r#trait,
                                path,
                            },
                        }
                    }
                    None => {
                        let msg = format!(
                            "Could not find a clause for `{tref:?}` in the item parameters"
                        );
                        warn(&msg);
                        ImplExprAtom::Error(msg)
                    }
                }
            }
            Ok(ImplSource::Builtin(BuiltinImplSource::Object { .. }, _)) => {
                nested = vec![];
                ImplExprAtom::Dyn
            }
            Ok(ImplSource::Builtin(_, _)) => {
                // Builtin impls currently don't need nested predicates.
                nested = vec![];
                ImplExprAtom::Builtin { r#trait: *tref }
            }
            Err(e) => {
                nested = vec![];
                let msg = format!(
                    "Could not find a clause for `{tref:?}` in the current context: `{e:?}`"
                );
                warn(&msg);
                ImplExprAtom::Error(msg)
            }
        };

        Ok(ImplExpr {
            r#impl: atom,
            args: nested,
            r#trait: *tref,
        })
    }

    /// Resolve the predicates required by the given item.
    pub fn resolve_item_predicates(
        &mut self,
        def_id: DefId,
        generics: GenericArgsRef<'tcx>,
        // Call back into hax-related code to display a nice warning.
        warn: &impl Fn(&str),
    ) -> Result<Vec<ImplExpr<'tcx>>, String> {
        let tcx = self.tcx;
        required_predicates(tcx, def_id)
            .predicates
            .iter()
            .map(|(clause, _span)| *clause)
            .filter_map(|clause| clause.as_trait_clause())
            .map(|trait_pred| trait_pred.map_bound(|p| p.trait_ref))
            // Substitute the item generics
            .map(|trait_ref| EarlyBinder::bind(trait_ref).instantiate(tcx, generics))
            // Resolve
            .map(|trait_ref| self.resolve(&trait_ref, warn))
            .collect()
    }
}

/// Attempts to resolve an obligation to an `ImplSource`. The result is a shallow `ImplSource`
/// resolution, meaning that we do not resolve all nested obligations on the impl. Note that type
/// check should guarantee to us that all nested obligations *could be* resolved if we wanted to.
///
/// This expects that `trait_ref` is fully normalized.
///
/// This is based on `rustc_traits::codegen::codegen_select_candidate` in rustc.
pub fn shallow_resolve_trait_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    trait_ref: PolyTraitRef<'tcx>,
) -> Result<ImplSource<'tcx, ()>, CodegenObligationError> {
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_middle::traits::CodegenObligationError;
    use rustc_middle::ty::TypeVisitableExt;
    use rustc_trait_selection::traits::{
        Obligation, ObligationCause, ObligationCtxt, SelectionContext, Unimplemented,
    };
    // Do the initial selection for the obligation. This yields the
    // shallow result we are looking for -- that is, what specific impl.
    let infcx = tcx.infer_ctxt().ignoring_regions().build();
    let mut selcx = SelectionContext::new(&infcx);

    let obligation_cause = ObligationCause::dummy();
    let obligation = Obligation::new(tcx, obligation_cause, param_env, trait_ref);

    let selection = match selcx.poly_select(&obligation) {
        Ok(Some(selection)) => selection,
        Ok(None) => return Err(CodegenObligationError::Ambiguity),
        Err(Unimplemented) => return Err(CodegenObligationError::Unimplemented),
        Err(_) => return Err(CodegenObligationError::FulfillmentError),
    };

    // Currently, we use a fulfillment context to completely resolve
    // all nested obligations. This is because they can inform the
    // inference of the impl's type parameters.
    // FIXME(-Znext-solver): Doesn't need diagnostics if new solver.
    let ocx = ObligationCtxt::new(&infcx);
    let impl_source = selection.map(|obligation| {
        ocx.register_obligation(obligation.clone());
        ()
    });

    let errors = ocx.select_all_or_error();
    if !errors.is_empty() {
        return Err(CodegenObligationError::FulfillmentError);
    }

    let impl_source = infcx.resolve_vars_if_possible(impl_source);
    let impl_source = tcx.erase_regions(impl_source);

    if impl_source.has_infer() {
        // Unused lifetimes on an impl get replaced with inference vars, but never resolved.
        return Err(CodegenObligationError::FulfillmentError);
    }

    Ok(impl_source)
}
