//! Trait resolution: given a trait reference, we track which local clause caused it to be true.
//! This module is independent from the rest of hax, in particular it doesn't use its
//! state-tracking machinery.

use itertools::Itertools;
use std::collections::{hash_map::Entry, HashMap};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::*;

use crate::traits::utils::erase_and_norm;

#[derive(Debug, Clone)]
pub enum PathChunk<'tcx> {
    AssocItem {
        item: AssocItem,
        predicate: PolyTraitPredicate<'tcx>,
        /// The nth predicate returned by `tcx.item_bounds`.
        index: usize,
    },
    Parent {
        predicate: PolyTraitPredicate<'tcx>,
        /// The nth predicate returned by `tcx.predicates_of`.
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
        /// `tcx.predicates_defined_on` starting from the parentmost item. If the item is an
        /// opaque type, we also append the predicates from `explicit_item_bounds` to this
        /// list.
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
    /// `tcx.predicates_defined_on` starting from the parentmost item. If the item is an opaque
    /// type, we also append the predicates from `explicit_item_bounds` to this list.
    Item(usize),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedTraitPred<'tcx> {
    pub origin: BoundPredicateOrigin,
    pub clause: PolyTraitPredicate<'tcx>,
}

/// The predicates to use as a starting point for resolving trait references within this
/// item. This is just like `TyCtxt::predicates_of`, but in the case of a trait or impl
/// item or closures, also includes the predicates defined on the parents.
fn initial_search_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: rustc_span::def_id::DefId,
) -> Vec<AnnotatedTraitPred<'tcx>> {
    let (predicates, self_pred) = super::utils::predicates_of_or_above(tcx, did);
    let predicates = predicates
        .into_iter()
        .enumerate()
        .map(|(i, clause)| AnnotatedTraitPred {
            origin: BoundPredicateOrigin::Item(i),
            clause,
        });
    let self_pred = self_pred.map(|clause| AnnotatedTraitPred {
        origin: BoundPredicateOrigin::SelfPred,
        clause,
    });

    self_pred.into_iter().chain(predicates).collect()
}

#[tracing::instrument(level = "trace", skip(tcx))]
fn parents_trait_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    pred: PolyTraitPredicate<'tcx>,
) -> Vec<PolyTraitPredicate<'tcx>> {
    let self_trait_ref = pred.to_poly_trait_ref();
    tcx.predicates_of(pred.def_id())
        .predicates
        .iter()
        // Substitute with the `self` args so that the clause makes sense in the
        // outside context.
        .map(|(clause, _span)| clause.instantiate_supertrait(tcx, self_trait_ref))
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
    /// Cache of trait refs to resolved impl expressions.
    resolution_cache: HashMap<PolyTraitRef<'tcx>, ImplExpr<'tcx>>,
}

impl<'tcx> PredicateSearcher<'tcx> {
    /// Initialize the elaborator with the predicates accessible within this item.
    pub fn new_for_owner(tcx: TyCtxt<'tcx>, owner_id: DefId) -> Self {
        let mut out = Self {
            tcx,
            param_env: tcx.param_env(owner_id),
            candidates: Default::default(),
            resolution_cache: Default::default(),
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
    fn add_associated_type_refs(&mut self, ty: Binder<'tcx, Ty<'tcx>>) {
        let tcx = self.tcx;
        // Note: We skip a binder but rebind it just after.
        let TyKind::Alias(AliasTyKind::Projection, alias_ty) = ty.skip_binder().kind() else {
            return;
        };
        let trait_ref = ty.rebind(alias_ty.trait_ref(tcx));

        // The predicate we're looking for is is `<T as Trait>::Type: OtherTrait`. We look up `T as
        // Trait` in the current context and add all the bounds on `Trait::Type` to our context.
        let Some(trait_candidate) = self.lookup(trait_ref) else {
            return;
        };

        let item_bounds = tcx
            // TODO: `item_bounds` can contain parent traits, we don't want them
            .item_bounds(alias_ty.def_id)
            .instantiate(tcx, alias_ty.args)
            .iter()
            .filter_map(|pred| pred.as_trait_clause())
            .enumerate();

        // Add all the bounds on the corresponding associated item.
        self.extend(item_bounds.map(|(index, pred)| {
            let mut candidate = Candidate {
                path: trait_candidate.path.clone(),
                pred,
                origin: trait_candidate.origin,
            };
            candidate.path.push(PathChunk::AssocItem {
                item: tcx.associated_item(alias_ty.def_id),
                predicate: pred,
                index,
            });
            candidate
        }));
    }

    /// Lookup a predicate in this set. If the predicate applies to an associated type, we
    /// add the relevant implied associated type bounds to the set as well.
    fn lookup(&mut self, target: PolyTraitRef<'tcx>) -> Option<Candidate<'tcx>> {
        let tcx = self.tcx;
        let target: PolyTraitPredicate = erase_and_norm(tcx, self.param_env, target).upcast(tcx);
        tracing::trace!("Looking for {target:?}");

        // Look up the predicate
        let ret = self.candidates.get(&target).cloned();
        if ret.is_some() {
            return ret;
        }

        // Add clauses related to associated type in the `Self` type of the predicate.
        self.add_associated_type_refs(target.self_ty());

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
        ret
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

        if let Some(impl_expr) = self.resolution_cache.get(tref) {
            return Ok(impl_expr.clone());
        }

        let tcx = self.tcx;
        let impl_source =
            copy_paste_from_rustc::codegen_select_candidate(tcx, (self.param_env, *tref));
        let atom = match impl_source {
            Ok(ImplSource::UserDefined(ImplSourceUserDefinedData {
                impl_def_id,
                args: generics,
                ..
            })) => ImplExprAtom::Concrete {
                def_id: impl_def_id,
                generics,
            },
            Ok(ImplSource::Param(_)) => match self.lookup(*tref) {
                Some(candidate) => {
                    let path = candidate.path;
                    let r#trait = candidate.origin.clause.to_poly_trait_ref();
                    match candidate.origin.origin {
                        BoundPredicateOrigin::SelfPred => ImplExprAtom::SelfImpl { r#trait, path },
                        BoundPredicateOrigin::Item(index) => ImplExprAtom::LocalBound {
                            predicate: candidate.origin.clause.upcast(tcx),
                            index,
                            r#trait,
                            path,
                        },
                    }
                }
                None => {
                    let msg =
                        format!("Could not find a clause for `{tref:?}` in the item parameters");
                    warn(&msg);
                    ImplExprAtom::Error(msg)
                }
            },
            Ok(ImplSource::Builtin(BuiltinImplSource::Object { .. }, _)) => ImplExprAtom::Dyn,
            Ok(ImplSource::Builtin(_, _)) => ImplExprAtom::Builtin { r#trait: *tref },
            Err(e) => {
                let msg = format!(
                    "Could not find a clause for `{tref:?}` in the current context: `{e:?}`"
                );
                warn(&msg);
                ImplExprAtom::Error(msg)
            }
        };

        let nested = match &impl_source {
            Ok(ImplSource::UserDefined(ImplSourceUserDefinedData { nested, .. })) => {
                nested.as_slice()
            }
            Ok(ImplSource::Param(nested)) => nested.as_slice(),
            // We ignore the contained obligations here. For example for `(): Send`, the
            // obligations contained would be `[(): Send]`, which leads to an infinite loop. There
            // might be important obligations here in other cases; we'll have to see if that comes
            // up.
            Ok(ImplSource::Builtin(_, _ignored)) => &[],
            Err(_) => &[],
        };
        let nested = nested
            .iter()
            // Only keep depth-1 obligations to avoid duplicate impl exprs.
            .filter(|obligation| obligation.recursion_depth == 1)
            .filter_map(|obligation| {
                obligation
                    .predicate
                    .as_trait_clause()
                    .map(|trait_ref| self.resolve(&trait_ref.map_bound(|p| p.trait_ref), warn))
            })
            .collect::<Result<_, _>>()?;

        let impl_expr = ImplExpr {
            r#impl: atom,
            args: nested,
            r#trait: *tref,
        };
        self.resolution_cache.insert(*tref, impl_expr.clone());
        Ok(impl_expr)
    }
}

mod copy_paste_from_rustc {
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_middle::traits::CodegenObligationError;
    use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
    use rustc_trait_selection::error_reporting::InferCtxtErrorExt;
    use rustc_trait_selection::traits::{
        Obligation, ObligationCause, ObligationCtxt, ScrubbedTraitError, SelectionContext,
        Unimplemented,
    };

    use crate::traits::utils::erase_and_norm;

    /// Attempts to resolve an obligation to an `ImplSource`. The result is
    /// a shallow `ImplSource` resolution, meaning that we do not
    /// (necessarily) resolve all nested obligations on the impl. Note
    /// that type check should guarantee to us that all nested
    /// obligations *could be* resolved if we wanted to.
    ///
    /// This also expects that `trait_ref` is fully normalized.
    pub fn codegen_select_candidate<'tcx>(
        tcx: TyCtxt<'tcx>,
        (param_env, trait_ref): (ty::ParamEnv<'tcx>, ty::PolyTraitRef<'tcx>),
    ) -> Result<rustc_trait_selection::traits::Selection<'tcx>, CodegenObligationError> {
        let trait_ref = erase_and_norm(tcx, param_env, trait_ref);

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
            Err(e) => {
                panic!(
                    "Encountered error `{:?}` selecting `{:?}` during codegen",
                    e, trait_ref
                )
            }
        };

        // Currently, we use a fulfillment context to completely resolve
        // all nested obligations. This is because they can inform the
        // inference of the impl's type parameters.
        // FIXME(-Znext-solver): Doesn't need diagnostics if new solver.
        let ocx = ObligationCtxt::new(&infcx);
        let impl_source = selection.map(|obligation| {
            ocx.register_obligation(obligation.clone());
            obligation
        });

        // In principle, we only need to do this so long as `impl_source`
        // contains unbound type parameters. It could be a slight
        // optimization to stop iterating early.
        let errors = ocx.select_all_or_error();
        if !errors.is_empty() {
            // `rustc_monomorphize::collector` assumes there are no type errors.
            // Cycle errors are the only post-monomorphization errors possible; emit them now so
            // `rustc_ty_utils::resolve_associated_item` doesn't return `None` post-monomorphization.
            for err in errors {
                if let ScrubbedTraitError::Cycle(cycle) = err {
                    infcx.err_ctxt().report_overflow_obligation_cycle(&cycle);
                }
            }
            return Err(CodegenObligationError::FulfillmentError);
        }

        let impl_source = infcx.resolve_vars_if_possible(impl_source);
        let impl_source = infcx.tcx.erase_regions(impl_source);

        if impl_source.has_infer() {
            // Unused lifetimes on an impl get replaced with inference vars, but never resolved,
            // causing the return value of a query to contain inference vars. We do not have a concept
            // for this and will in fact ICE in stable hashing of the return value. So bail out instead.
            infcx.tcx.dcx().has_errors().unwrap();
            return Err(CodegenObligationError::FulfillmentError);
        }

        Ok(impl_source)
    }
}
