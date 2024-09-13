use crate::prelude::*;

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: search_clause::PathChunk<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprPathChunk {
    AssocItem {
        item: AssocItem,
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        index: usize,
    },
    Parent {
        predicate: Binder<TraitPredicate>,
        #[value(<_ as SInto<_, Clause>>::sinto(predicate, s).id)]
        predicate_id: PredicateId,
        index: usize,
    },
}

/// The source of a particular trait implementation. Most often this is either `Concrete` for a
/// concrete `impl Trait for Type {}` item, or `LocalBound` for a context-bound `where T: Trait`.
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub enum ImplExprAtom {
    /// A concrete `impl Trait for Type {}` item.
    Concrete {
        id: GlobalIdent,
        generics: Vec<GenericArg>,
    },
    /// A context-bound clause like `where T: Trait`.
    LocalBound {
        predicate_id: PredicateId,
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// The automatic clause `Self: Trait` present inside a `impl Trait for Type {}` item.
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
    Builtin { r#trait: TraitRef },
    /// Anything else. Currently used for trait upcasting and trait aliases.
    Todo(String),
}

/// An `ImplExpr` describes the full data of a trait implementation. Because of generics, this may
/// need to combine several concrete trait implementation items. For example, `((1u8, 2u8),
/// "hello").clone()` combines the generic implementation of `Clone` for `(A, B)` with the
/// concrete implementations for `u8` and `&str`, represented as a tree.
#[derive_group(Serializers)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, JsonSchema)]
pub struct ImplExpr {
    /// The trait this is an impl for.
    pub r#trait: TraitRef,
    /// The kind of implemention of the root of the tree.
    pub r#impl: ImplExprAtom,
    /// A list of `ImplExpr`s required to fully specify the trait references in `impl`.
    pub args: Vec<ImplExpr>,
}

#[cfg(feature = "rustc")]
pub mod rustc {
    use super::*;
    // FIXME: this has visibility `pub(crate)` only because of https://github.com/rust-lang/rust/issues/83049
    pub(crate) mod search_clause {
        use crate::prelude::UnderOwnerState;
        use crate::rustc_utils::*;
        use rustc_middle::ty::*;

        fn predicates_to_poly_trait_predicates<'tcx>(
            tcx: TyCtxt<'tcx>,
            predicates: impl Iterator<Item = Predicate<'tcx>>,
            generics: GenericArgsRef<'tcx>,
        ) -> impl Iterator<Item = PolyTraitPredicate<'tcx>> {
            predicates
                .map(move |pred| pred.kind().subst(tcx, generics))
                .filter_map(|pred| pred.as_poly_trait_predicate())
        }

        #[derive(Clone, Debug)]
        pub enum PathChunk<'tcx> {
            AssocItem {
                item: AssocItem,
                predicate: PolyTraitPredicate<'tcx>,
                index: usize,
            },
            Parent {
                predicate: PolyTraitPredicate<'tcx>,
                index: usize,
            },
        }
        pub type Path<'tcx> = Vec<PathChunk<'tcx>>;

        /// Custom equality on `Predicate`s.
        ///
        /// Sometimes Rustc inserts extra generic arguments: I noticed
        /// some `__H` second argument given to core::hash::Hash for
        /// instance. `__H` seems to be inserted in [1]. Such extra
        /// arguments seems to be ignored by `default_print_def_path` [2].
        ///
        /// Hence, for now, equality is decided by comparing the debug
        /// string representations of `Predicate`s.
        ///
        /// Note there exist also predicates that are different,
        /// `Eq`-wise, but whose `sinto` counterpart are equal.
        ///
        /// TODO: figure out how to implement this function in a sane way.
        ///
        /// [1]: https://github.com/rust-lang/rust/blob/b0889cb4ed0e6f3ed9f440180678872b02e7052c/compiler/rustc_builtin_macros/src/deriving/hash.rs#L20
        /// [2]: https://github.com/rust-lang/rust/blob/b0889cb4ed0e6f3ed9f440180678872b02e7052c/compiler/rustc_middle/src/ty/print/mod.rs#L141
        fn predicate_equality<'tcx, S: UnderOwnerState<'tcx>>(
            x: Predicate<'tcx>,
            y: Predicate<'tcx>,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
            s: &S,
        ) -> bool {
            let tcx = s.base().tcx;
            let erase_and_norm =
                |x| tcx.erase_regions(tcx.try_normalize_erasing_regions(param_env, x).unwrap_or(x));
            // Lifetime and constantness are irrelevant when resolving instances
            let x = erase_and_norm(x);
            let y = erase_and_norm(y);
            let sx = format!("{:?}", x.kind().skip_binder());
            let sy = format!("{:?}", y.kind().skip_binder());
            let result = sx == sy;
            const DEBUG: bool = false;
            if DEBUG && result {
                use crate::{Predicate, SInto};
                let xs: Predicate = x.sinto(s);
                let ys: Predicate = y.sinto(s);
                if x != y {
                    eprintln!(
                        "######################## predicate_equality ########################"
                    );
                    eprintln!("x={:#?}", x);
                    eprintln!("y={:#?}", y);
                    eprintln!(
                        "########################        sinto       ########################"
                    );
                    eprintln!("sinto(x)={:#?}", xs);
                    eprintln!("sinto(y)={:#?}", ys);
                }
            }
            result
        }

        #[extension_traits::extension(pub trait TraitPredicateExt)]
        impl<'tcx, S: UnderOwnerState<'tcx>> PolyTraitPredicate<'tcx> {
            #[tracing::instrument(level = "trace", skip(s))]
            fn parents_trait_predicates(self, s: &S) -> Vec<(usize, PolyTraitPredicate<'tcx>)> {
                let tcx = s.base().tcx;
                let predicates = tcx
                    .predicates_defined_on_or_above(self.def_id())
                    .into_iter()
                    .map(|apred| apred.predicate);
                predicates_to_poly_trait_predicates(
                    tcx,
                    predicates,
                    self.skip_binder().trait_ref.args,
                )
                .enumerate()
                .collect()
            }
            #[tracing::instrument(level = "trace", skip(s))]
            fn associated_items_trait_predicates(
                self,
                s: &S,
            ) -> Vec<(
                AssocItem,
                EarlyBinder<'tcx, Vec<(usize, PolyTraitPredicate<'tcx>)>>,
            )> {
                let tcx = s.base().tcx;
                tcx.associated_items(self.def_id())
                    .in_definition_order()
                    .filter(|item| item.kind == AssocKind::Type)
                    .copied()
                    .map(|item| {
                        let bounds = tcx.item_bounds(item.def_id).map_bound(|clauses| {
                            predicates_to_poly_trait_predicates(
                                tcx,
                                clauses.into_iter().map(|clause| clause.as_predicate()),
                                self.skip_binder().trait_ref.args,
                            )
                            .enumerate()
                            .collect()
                        });
                        (item, bounds)
                    })
                    .collect()
            }
        }

        #[tracing::instrument(level = "trace", skip(s, param_env))]
        pub fn path_to<'tcx, S: UnderOwnerState<'tcx>>(
            starting_points: &[AnnotatedPredicate<'tcx>],
            s: &S,
            target: PolyTraitRef<'tcx>,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
        ) -> Option<(Path<'tcx>, AnnotatedPredicate<'tcx>)> {
            let tcx = s.base().tcx;

            /// A candidate projects `self` along a path reaching some
            /// predicate. A candidate is selected when its predicate
            /// is the one expected, aka `target`.
            #[derive(Debug)]
            struct Candidate<'tcx> {
                path: Path<'tcx>,
                pred: PolyTraitPredicate<'tcx>,
                origin: AnnotatedPredicate<'tcx>,
            }

            use std::collections::VecDeque;
            let mut candidates: VecDeque<Candidate<'tcx>> = starting_points
                .into_iter()
                .filter_map(|pred| {
                    let clause = pred.predicate.as_trait_clause();
                    clause.map(|clause| Candidate {
                        path: vec![],
                        pred: clause,
                        origin: *pred,
                    })
                })
                .collect();

            let target_pred = target.upcast(tcx);
            let mut seen = std::collections::HashSet::new();

            while let Some(candidate) = candidates.pop_front() {
                {
                    // If a predicate was already seen, we know it is
                    // not the one we are looking for: we skip it.
                    if seen.contains(&candidate.pred) {
                        continue;
                    }
                    seen.insert(candidate.pred);
                }

                // if the candidate equals the target, let's return its path
                if predicate_equality(candidate.pred.upcast(tcx), target_pred, param_env, s) {
                    return Some((candidate.path, candidate.origin));
                }

                // otherwise, we add to the queue all paths reachable from the candidate
                for (index, parent_pred) in candidate.pred.parents_trait_predicates(s) {
                    let mut path = candidate.path.clone();
                    path.push(PathChunk::Parent {
                        predicate: parent_pred,
                        index,
                    });
                    candidates.push_back(Candidate {
                        pred: parent_pred,
                        path,
                        origin: candidate.origin,
                    });
                }
                for (item, binder) in candidate.pred.associated_items_trait_predicates(s) {
                    for (index, parent_pred) in binder.skip_binder().into_iter() {
                        let mut path = candidate.path.clone();
                        path.push(PathChunk::AssocItem {
                            item,
                            predicate: parent_pred,
                            index,
                        });
                        candidates.push_back(Candidate {
                            pred: parent_pred,
                            path,
                            origin: candidate.origin,
                        });
                    }
                }
            }
            None
        }
    }

    impl ImplExprAtom {
        fn with_args(self, args: Vec<ImplExpr>, r#trait: TraitRef) -> ImplExpr {
            ImplExpr {
                r#impl: self,
                args,
                r#trait,
            }
        }
    }

    #[tracing::instrument(level = "trace", skip(s))]
    fn impl_exprs<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        obligations: &Vec<
            rustc_trait_selection::traits::Obligation<'tcx, rustc_middle::ty::Predicate<'tcx>>,
        >,
    ) -> Vec<ImplExpr> {
        obligations
            .into_iter()
            .flat_map(|obligation| {
                obligation
                    .predicate
                    .kind()
                    .as_poly_trait_predicate()
                    .map(|trait_ref| {
                        trait_ref
                            .map_bound(|p| p.trait_ref)
                            .impl_expr(s, obligation.param_env)
                    })
            })
            .collect()
    }

    pub trait IntoImplExpr<'tcx> {
        fn impl_expr<S: UnderOwnerState<'tcx>>(
            &self,
            s: &S,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
        ) -> ImplExpr;
    }

    impl<'tcx> IntoImplExpr<'tcx> for rustc_middle::ty::PolyTraitPredicate<'tcx> {
        fn impl_expr<S: UnderOwnerState<'tcx>>(
            &self,
            s: &S,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
        ) -> ImplExpr {
            use rustc_middle::ty::ToPolyTraitRef;
            self.to_poly_trait_ref().impl_expr(s, param_env)
        }
    }
    impl<'tcx> IntoImplExpr<'tcx> for rustc_middle::ty::PolyTraitRef<'tcx> {
        #[tracing::instrument(level = "trace", skip(s, param_env))]
        fn impl_expr<S: UnderOwnerState<'tcx>>(
            &self,
            s: &S,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
        ) -> ImplExpr {
            use rustc_trait_selection::traits::*;
            let trait_ref: Binder<TraitRef> = self.sinto(s);
            let trait_ref = trait_ref.value;
            match select_trait_candidate(s, param_env, *self) {
                ImplSource::UserDefined(ImplSourceUserDefinedData {
                    impl_def_id,
                    args: generics,
                    nested,
                }) => ImplExprAtom::Concrete {
                    id: impl_def_id.sinto(s),
                    generics: generics.sinto(s),
                }
                .with_args(impl_exprs(s, &nested), trait_ref),
                ImplSource::Param(nested) => {
                    let tcx = s.base().tcx;
                    let predicates = tcx.predicates_defined_on_or_above(s.owner_id());
                    let Some((path, apred)) =
                        search_clause::path_to(&predicates, s, self.clone(), param_env)
                    else {
                        supposely_unreachable_fatal!(s, "ImplExprPredNotFound"; {
                            self, nested, predicates, trait_ref
                        })
                    };

                    use rustc_middle::ty::ToPolyTraitRef;
                    let r#trait = apred
                        .predicate
                        .as_trait_clause()
                        .s_unwrap(s)
                        .to_poly_trait_ref()
                        .sinto(s);
                    let path = path.sinto(s);
                    if apred.is_extra_self_predicate {
                        ImplExprAtom::SelfImpl { r#trait, path }
                            .with_args(impl_exprs(s, &nested), trait_ref)
                    } else {
                        ImplExprAtom::LocalBound {
                            predicate_id: apred.predicate.sinto(s).id,
                            r#trait,
                            path,
                        }
                        .with_args(impl_exprs(s, &nested), trait_ref)
                    }
                }
                // We ignore the contained obligations here. For example for `(): Send`, the
                // obligations contained would be `[(): Send]`, which leads to an infinite loop. There
                // might be important obligation shere inother cases; we'll have to see if that comes
                // up.
                ImplSource::Builtin(source, _ignored) => {
                    let atom = match source {
                        BuiltinImplSource::Object { .. } => ImplExprAtom::Dyn,
                        _ => ImplExprAtom::Builtin {
                            r#trait: trait_ref.clone(),
                        },
                    };
                    atom.with_args(vec![], trait_ref)
                }
            }
        }
    }

    /// Given a clause `clause` in the context of some impl. block
    /// `impl_did`, susbts correctly `Self` from `clause` and (1) derive a
    /// `Clause` and (2) resolve an `ImplExpr`.
    pub fn super_clause_to_clause_and_impl_expr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        impl_did: rustc_span::def_id::DefId,
        clause: rustc_middle::ty::Clause<'tcx>,
        span: rustc_span::Span,
    ) -> Option<(Clause, ImplExpr, Span)> {
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
        let impl_expr = new_clause
            .as_predicate()
            .as_trait_clause()?
            .impl_expr(s, s.param_env());
        let mut new_clause_no_binder = new_clause.sinto(s);
        new_clause_no_binder.id = original_predicate_id;
        Some((new_clause_no_binder, impl_expr, span.sinto(s)))
    }

    #[tracing::instrument(level = "trace", skip(s, param_env))]
    pub fn select_trait_candidate<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        param_env: rustc_middle::ty::ParamEnv<'tcx>,
        trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
    ) -> rustc_trait_selection::traits::Selection<'tcx> {
        let tcx = s.base().tcx;
        match copy_paste_from_rustc::codegen_select_candidate(tcx, (param_env, trait_ref)) {
            Ok(selection) => selection,
            Err(error) => fatal!(
                s,
                "Cannot handle error `{:?}` selecting `{:?}`",
                error,
                trait_ref
            ),
        }
    }

    pub mod copy_paste_from_rustc {
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
            let trait_ref = tcx.normalize_erasing_regions(param_env, trait_ref);

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
#[cfg(feature = "rustc")]
pub use self::rustc::*;
