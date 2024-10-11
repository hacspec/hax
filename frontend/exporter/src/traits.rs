use crate::prelude::*;

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc::PathChunk<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprPathChunk {
    AssocItem {
        item: AssocItem,
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        /// The nth predicate returned by `tcx.item_bounds`.
        index: usize,
    },
    Parent {
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        /// The nth predicate returned by `tcx.predicates_of`.
        index: usize,
    },
}

/// The source of a particular trait implementation. Most often this is either `Concrete` for a
/// concrete `impl Trait for Type {}` item, or `LocalBound` for a context-bound `where T: Trait`.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc::ImplExprAtom<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprAtom {
    /// A concrete `impl Trait for Type {}` item.
    Concrete {
        #[from(def_id)]
        id: GlobalIdent,
        generics: Vec<GenericArg>,
    },
    /// A context-bound clause like `where T: Trait`.
    LocalBound {
        #[not_in_source]
        #[value({
            let Self::LocalBound { predicate, .. } = self else { unreachable!() };
            predicate.sinto(s).id
        })]
        predicate_id: PredicateId,
        /// The nth (non-self) predicate found for this item. We use predicates from
        /// `tcx.predicates_defined_on` starting from the parentmost item. If the item is an opaque
        /// type, we also append the predicates from `explicit_item_bounds` to this list.
        index: usize,
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// The implicit `Self: Trait` clause present inside a `trait Trait {}` item.
    // TODO: should we also get that clause for trait impls?
    SelfImpl {
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// `dyn Trait` is a wrapped value with a virtual table for trait
    /// `Trait`.  In other words, a value `dyn Trait` is a dependent
    /// triple that gathers a type τ, a value of type τ and an
    /// instance of type `Trait`.
    /// `dyn Trait` implements `Trait` using a built-in implementation; this refers to that
    /// built-in implementation.
    Dyn,
    /// A built-in trait whose implementation is computed by the compiler, such as `Sync`.
    Builtin { r#trait: Binder<TraitRef> },
    /// An error happened while resolving traits.
    Error(String),
}

/// An `ImplExpr` describes the full data of a trait implementation. Because of generics, this may
/// need to combine several concrete trait implementation items. For example, `((1u8, 2u8),
/// "hello").clone()` combines the generic implementation of `Clone` for `(A, B)` with the
/// concrete implementations for `u8` and `&str`, represented as a tree.
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema, AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: rustc::ImplExpr<'tcx>, state: S as s)]
pub struct ImplExpr {
    /// The trait this is an impl for.
    pub r#trait: Binder<TraitRef>,
    /// The kind of implemention of the root of the tree.
    pub r#impl: ImplExprAtom,
    /// A list of `ImplExpr`s required to fully specify the trait references in `impl`.
    pub args: Vec<ImplExpr>,
}

#[cfg(feature = "rustc")]
pub mod rustc {
    use rustc_hir::def::DefKind;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::*;

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

    /// Just like `TyCtxt::predicates_of`, but in the case of a trait or impl item or closures,
    /// also includes the predicates defined on the parents. Also this returns the special
    /// `Self` clause separately.
    fn predicates_of_or_above<'tcx>(
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

    /// The predicates to use as a starting point for resolving trait references within this
    /// item. This is just like `TyCtxt::predicates_of`, but in the case of a trait or impl
    /// item or closures, also includes the predicates defined on the parents.
    fn initial_search_predicates<'tcx>(
        tcx: TyCtxt<'tcx>,
        did: rustc_span::def_id::DefId,
    ) -> Vec<AnnotatedTraitPred<'tcx>> {
        let (predicates, self_pred) = predicates_of_or_above(tcx, did);
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

    // FIXME: this has visibility `pub(crate)` only because of https://github.com/rust-lang/rust/issues/83049
    pub(crate) mod search_clause {
        use super::{AnnotatedTraitPred, Path, PathChunk};
        use itertools::Itertools;
        use rustc_hir::def_id::DefId;
        use rustc_middle::ty::*;
        use std::collections::{hash_map::Entry, HashMap};

        /// Erase all regions. Largely copied from `tcx.erase_regions`.
        fn erase_all_regions<'tcx, T>(tcx: TyCtxt<'tcx>, value: T) -> T
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
        pub(crate) fn erase_and_norm<'tcx, T>(
            tcx: TyCtxt<'tcx>,
            param_env: ParamEnv<'tcx>,
            x: T,
        ) -> T
        where
            T: TypeFoldable<TyCtxt<'tcx>> + Copy,
        {
            erase_all_regions(
                tcx,
                tcx.try_normalize_erasing_regions(param_env, x).unwrap_or(x),
            )
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
        struct PredicateSearcher<'tcx> {
            tcx: TyCtxt<'tcx>,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
            candidates: HashMap<PolyTraitPredicate<'tcx>, Candidate<'tcx>>,
        }

        impl<'tcx> PredicateSearcher<'tcx> {
            /// Initialize the elaborator with the predicates accessible within this item.
            fn new_for_owner(
                tcx: TyCtxt<'tcx>,
                param_env: rustc_middle::ty::ParamEnv<'tcx>,
                owner_id: DefId,
            ) -> Self {
                let mut out = Self {
                    tcx,
                    param_env,
                    candidates: Default::default(),
                };
                out.extend(
                    super::initial_search_predicates(tcx, owner_id)
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

            /// Lookup a predicate in this set. If the predicate applies to an associated type, we
            /// add the relevant implied associated type bounds to the set as well.
            fn lookup(&mut self, target: PolyTraitRef<'tcx>) -> Option<&Candidate<'tcx>> {
                let tcx = self.tcx;
                let target: PolyTraitPredicate =
                    erase_and_norm(tcx, self.param_env, target).upcast(tcx);

                // The predicate is `<T as Trait>::Type: OtherTrait`. We look up `T as Trait` in
                // the current context and add all the bounds on `Trait::Type` to our context.
                // Note: We skip a binder but rebind it just after.
                if let TyKind::Alias(AliasTyKind::Projection, alias_ty) =
                    target.self_ty().skip_binder().kind()
                {
                    let trait_ref = target.rebind(alias_ty.trait_ref(tcx));
                    // Recursively look up the trait ref inside `self`.
                    let trait_candidate = self.lookup(trait_ref)?.clone();
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

                tracing::trace!("Looking for {target:?}");
                let ret = self.candidates.get(&target);
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
        }

        #[tracing::instrument(level = "trace", skip(tcx, param_env))]
        pub(super) fn path_to<'tcx>(
            tcx: TyCtxt<'tcx>,
            owner_id: DefId,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
            target: PolyTraitRef<'tcx>,
        ) -> Option<(Path<'tcx>, AnnotatedTraitPred<'tcx>)> {
            let mut searcher = PredicateSearcher::new_for_owner(tcx, param_env, owner_id);
            let candidate = searcher.lookup(target)?;
            Some((candidate.path.clone(), candidate.origin))
        }
    }

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

    #[tracing::instrument(level = "trace", skip(tcx, warn))]
    fn impl_exprs<'tcx>(
        tcx: TyCtxt<'tcx>,
        owner_id: DefId,
        obligations: &[rustc_trait_selection::traits::Obligation<
            'tcx,
            rustc_middle::ty::Predicate<'tcx>,
        >],
        warn: &impl Fn(&str),
    ) -> Result<Vec<ImplExpr<'tcx>>, String> {
        obligations
            .iter()
            // Only keep depth-1 obligations to avoid duplicate impl exprs.
            .filter(|obligation| obligation.recursion_depth == 1)
            .filter_map(|obligation| {
                obligation.predicate.as_trait_clause().map(|trait_ref| {
                    impl_expr(
                        tcx,
                        owner_id,
                        obligation.param_env,
                        &trait_ref.map_bound(|p| p.trait_ref),
                        warn,
                    )
                })
            })
            .collect()
    }

    #[tracing::instrument(level = "trace", skip(tcx, param_env, warn))]
    pub(super) fn impl_expr<'tcx>(
        tcx: TyCtxt<'tcx>,
        owner_id: DefId,
        param_env: rustc_middle::ty::ParamEnv<'tcx>,
        tref: &rustc_middle::ty::PolyTraitRef<'tcx>,
        // Call back into hax-related code to display a nice warning.
        warn: &impl Fn(&str),
    ) -> Result<ImplExpr<'tcx>, String> {
        use rustc_trait_selection::traits::{
            BuiltinImplSource, ImplSource, ImplSourceUserDefinedData,
        };

        let impl_source = copy_paste_from_rustc::codegen_select_candidate(tcx, (param_env, *tref));
        let atom = match impl_source {
            Ok(ImplSource::UserDefined(ImplSourceUserDefinedData {
                impl_def_id,
                args: generics,
                ..
            })) => ImplExprAtom::Concrete {
                def_id: impl_def_id,
                generics,
            },
            Ok(ImplSource::Param(_)) => {
                match search_clause::path_to(tcx, owner_id, param_env, *tref) {
                    Some((path, apred)) => {
                        let r#trait = apred.clause.to_poly_trait_ref();
                        match apred.origin {
                            BoundPredicateOrigin::SelfPred => {
                                ImplExprAtom::SelfImpl { r#trait, path }
                            }
                            BoundPredicateOrigin::Item(index) => ImplExprAtom::LocalBound {
                                predicate: apred.clause.upcast(tcx),
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
        let nested = impl_exprs(tcx, owner_id, nested, warn)?;

        Ok(ImplExpr {
            r#impl: atom,
            args: nested,
            r#trait: *tref,
        })
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
        ) -> Result<rustc_trait_selection::traits::Selection<'tcx>, CodegenObligationError>
        {
            let trait_ref = super::search_clause::erase_and_norm(tcx, param_env, trait_ref);

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
}

/// Given a clause `clause` in the context of some impl block `impl_did`, susbts correctly `Self`
/// from `clause` and (1) derive a `Clause` and (2) resolve an `ImplExpr`.
#[cfg(feature = "rustc")]
pub fn super_clause_to_clause_and_impl_expr<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    impl_did: rustc_span::def_id::DefId,
    clause: rustc_middle::ty::Clause<'tcx>,
    span: rustc_span::Span,
) -> Option<(Clause, ImplExpr, Span)> {
    use rustc_middle::ty::ToPolyTraitRef;
    let tcx = s.base().tcx;
    let impl_trait_ref = tcx
        .impl_trait_ref(impl_did)
        .map(|binder| rustc_middle::ty::Binder::dummy(binder.instantiate_identity()))?;
    let original_predicate_id = {
        // We don't want the id of the substituted clause id, but the
        // original clause id (with, i.e., `Self`)
        let s = &with_owner_id(s.base(), (), (), impl_trait_ref.def_id());
        clause.sinto(s).id
    };
    let new_clause = clause.instantiate_supertrait(tcx, impl_trait_ref);
    let impl_expr = solve_trait(
        s,
        new_clause
            .as_predicate()
            .as_trait_clause()?
            .to_poly_trait_ref(),
    );
    let mut new_clause_no_binder = new_clause.sinto(s);
    new_clause_no_binder.id = original_predicate_id;
    Some((new_clause_no_binder, impl_expr, span.sinto(s)))
}

/// This is the entrypoint of the solving.
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s))]
pub fn solve_trait<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> ImplExpr {
    use crate::ParamEnv;
    let warn = |msg: &str| {
        if !s.base().ty_alias_mode {
            crate::warning!(s, "{}", msg)
        }
    };
    match rustc::impl_expr(s.base().tcx, s.owner_id(), s.param_env(), &trait_ref, &warn) {
        Ok(x) => x.sinto(s),
        Err(e) => crate::fatal!(s, "{}", e),
    }
}

/// Solve the trait obligations for a specific item use (for example, a method call, an ADT, etc.).
///
/// [predicates]: optional predicates, in case we want to solve custom predicates (instead of the
/// ones returned by [TyCtxt::predicates_defined_on].
#[cfg(feature = "rustc")]
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: rustc_hir::def_id::DefId,
    generics: rustc_middle::ty::GenericArgsRef<'tcx>,
    predicates: Option<rustc_middle::ty::GenericPredicates<'tcx>>,
) -> Vec<ImplExpr> {
    let tcx = s.base().tcx;
    let param_env = s.param_env();

    let mut impl_exprs = Vec::new();

    // Lookup the predicates and iter through them: we want to solve all the
    // trait requirements.
    // IMPORTANT: we use [TyCtxt::predicates_defined_on] and not [TyCtxt::predicated_of]
    let predicates = match predicates {
        None => tcx.predicates_defined_on(def_id),
        Some(preds) => preds,
    };
    for (pred, _) in predicates.predicates {
        // Explore only the trait predicates
        if let Some(trait_clause) = pred.as_trait_clause() {
            let poly_trait_ref = trait_clause.map_bound(|clause| clause.trait_ref);
            // Apply the substitution
            let poly_trait_ref =
                rustc_middle::ty::EarlyBinder::bind(poly_trait_ref).instantiate(tcx, generics);
            // Warning: this erases regions. We don't really have a way to normalize without
            // erasing regions, but this may cause problems in trait solving if there are trait
            // impls that include `'static` lifetimes.
            let poly_trait_ref = tcx
                .try_normalize_erasing_regions(param_env, poly_trait_ref)
                .unwrap_or(poly_trait_ref);
            let impl_expr = solve_trait(s, poly_trait_ref);
            impl_exprs.push(impl_expr);
        }
    }
    impl_exprs
}

/// Retrieve the `Self: Trait` clause for a trait associated item.
#[cfg(feature = "rustc")]
pub fn self_clause_for_item<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    assoc: &rustc_middle::ty::AssocItem,
    generics: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<ImplExpr> {
    let tcx = s.base().tcx;

    // Retrieve the trait
    let tr_def_id = tcx.trait_of_item(assoc.def_id)?;

    // Create the reference to the trait
    use rustc_middle::ty::TraitRef;
    let tr_generics = tcx.generics_of(tr_def_id);
    let generics = generics.truncate_to(tcx, tr_generics);
    let tr_ref = TraitRef::new(tcx, tr_def_id, generics);
    let tr_ref = rustc_middle::ty::Binder::dummy(tr_ref);

    // Solve
    Some(solve_trait(s, tr_ref))
}
