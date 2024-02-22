use crate::prelude::*;

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: search_clause::PathChunk<'tcx>, state: S as tcx)]
#[derive(
    Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
pub enum ImplExprPathChunk {
    AssocItem {
        item: AssocItem,
        predicate: TraitPredicate,
        index: usize,
    },
    Parent {
        predicate: TraitPredicate,
        index: usize,
    },
}

#[derive(
    Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
pub enum ImplExprAtom {
    Concrete {
        id: GlobalIdent,
        generics: Vec<GenericArg>,
    },
    LocalBound {
        clause_id: u64,
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    SelfImpl {
        r#trait: Binder<TraitRef>,
        path: Vec<ImplExprPathChunk>,
    },
    /// `dyn TRAIT` is a wrapped value with a virtual table for trait
    /// `TRAIT`.  In other words, a value `dyn TRAIT` is a dependent
    /// triple that gathers a type τ, a value of type τ and an
    /// instance of type `TRAIT`.
    Dyn {
        r#trait: TraitRef,
    },
    Builtin {
        r#trait: TraitRef,
    },
    FnPointer {
        fn_ty: Box<Ty>,
    },
    Closure {
        closure_def_id: DefId,
        parent_substs: Vec<GenericArg>,
        signature: Box<PolyFnSig>,
    },
    Todo(String),
}

#[derive(
    Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
pub struct ImplExpr {
    pub r#impl: ImplExprAtom,
    pub args: Box<Vec<ImplExpr>>,
    pub r#trait: TraitRef,
}

mod search_clause {
    use super::SubstBinder;
    use crate::prelude::UnderOwnerState;
    use crate::rustc_utils::TyCtxtExtPredOrAbove;
    use rustc_middle::ty::*;

    fn predicates_to_trait_predicates<'tcx>(
        tcx: TyCtxt<'tcx>,
        predicates: impl Iterator<Item = Predicate<'tcx>>,
        substs: subst::SubstsRef<'tcx>,
    ) -> impl Iterator<Item = TraitPredicate<'tcx>> {
        predicates
            .map(move |pred| pred.kind().subst(tcx, substs))
            .filter_map(|x| match x {
                PredicateKind::Clause(Clause::Trait(c)) => Some(c),
                _ => None,
            })
    }

    #[derive(Clone, Debug)]
    pub enum PathChunk<'tcx> {
        AssocItem {
            item: AssocItem,
            predicate: TraitPredicate<'tcx>,
            index: usize,
        },
        Parent {
            predicate: TraitPredicate<'tcx>,
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
        let x = tcx.try_normalize_erasing_regions(param_env, x).unwrap_or(x);
        let y = tcx.try_normalize_erasing_regions(param_env, y).unwrap_or(y);
        let result = format!("{:?}", x) == format!("{:?}", y);
        const DEBUG: bool = false;
        if DEBUG && result {
            use crate::{Predicate, SInto};
            let xs: Predicate = x.sinto(s);
            let ys: Predicate = y.sinto(s);
            if x != y {
                eprintln!("######################## predicate_equality ########################");
                eprintln!("x={:#?}", x);
                eprintln!("y={:#?}", y);
                eprintln!("########################        sinto       ########################");
                eprintln!("sinto(x)={:#?}", xs);
                eprintln!("sinto(y)={:#?}", ys);
            }
        }
        result
    }

    #[extension_traits::extension(pub trait TraitPredicateExt)]
    impl<'tcx, S: UnderOwnerState<'tcx>> TraitPredicate<'tcx> {
        fn parents_trait_predicates(self, s: &S) -> Vec<(usize, TraitPredicate<'tcx>)> {
            let tcx = s.base().tcx;
            let predicates = tcx
                .predicates_defined_on_or_above(self.def_id())
                .into_iter()
                .map(|apred| apred.predicate);
            predicates_to_trait_predicates(tcx, predicates, self.trait_ref.substs)
                .enumerate()
                .collect()
        }
        fn associated_items_trait_predicates(
            self,
            s: &S,
        ) -> Vec<(
            AssocItem,
            subst::EarlyBinder<Vec<(usize, TraitPredicate<'tcx>)>>,
        )> {
            let tcx = s.base().tcx;
            tcx.associated_items(self.def_id())
                .in_definition_order()
                .filter(|item| item.kind == AssocKind::Type)
                .copied()
                .map(|item| {
                    let bounds = tcx.item_bounds(item.def_id).map_bound(|predicates| {
                        predicates_to_trait_predicates(
                            tcx,
                            predicates.into_iter(),
                            self.trait_ref.substs,
                        )
                        .enumerate()
                        .collect()
                    });
                    (item, bounds)
                })
                .collect()
        }

        fn path_to(
            self,
            s: &S,
            target: PolyTraitRef<'tcx>,
            param_env: rustc_middle::ty::ParamEnv<'tcx>,
        ) -> Option<Path<'tcx>> {
            let tcx = s.base().tcx;
            if predicate_equality(
                self.to_predicate(tcx),
                target.to_predicate(tcx),
                param_env,
                s,
            ) {
                return Some(vec![]);
            }

            let recurse = |p: Self| {
                if p == self {
                    return None;
                }
                p.path_to(s, target, param_env)
            };
            fn cons<T>(hd: T, tail: Vec<T>) -> Vec<T> {
                vec![hd].into_iter().chain(tail.into_iter()).collect()
            }
            self.parents_trait_predicates(s)
                .into_iter()
                .filter_map(|(index, p)| {
                    recurse(p).map(|path| {
                        cons(
                            PathChunk::Parent {
                                predicate: p,
                                index,
                            },
                            path,
                        )
                    })
                })
                .max_by_key(|path| path.len())
                .or_else(|| {
                    self.associated_items_trait_predicates(s)
                        .into_iter()
                        .filter_map(|(item, binder)| {
                            binder.skip_binder().into_iter().find_map(|(index, p)| {
                                recurse(p).map(|path| {
                                    cons(
                                        PathChunk::AssocItem {
                                            item,
                                            predicate: p,
                                            index,
                                        },
                                        path,
                                    )
                                })
                            })
                        })
                        .max_by_key(|path| path.len())
                })
        }
    }
}

impl ImplExprAtom {
    fn with_args(self, args: Vec<ImplExpr>, r#trait: TraitRef) -> ImplExpr {
        ImplExpr {
            r#impl: self,
            args: Box::new(args),
            r#trait,
        }
    }
}

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
                .as_poly_trait_ref()
                .map(|trait_ref| trait_ref.impl_expr(s, obligation.param_env))
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

impl<'tcx> IntoImplExpr<'tcx> for rustc_middle::ty::PolyTraitRef<'tcx> {
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
                substs,
                nested,
            }) => ImplExprAtom::Concrete {
                id: impl_def_id.sinto(s),
                generics: substs.sinto(s),
            }
            .with_args(impl_exprs(s, &nested), trait_ref),
            ImplSource::Param(nested, _constness) => {
                use search_clause::TraitPredicateExt;
                let tcx = s.base().tcx;
                let predicates = &tcx.predicates_defined_on_or_above(s.owner_id());
                let Some((apred, path)) = predicates.into_iter().find_map(|apred| {
                    apred
                        .predicate
                        .to_opt_poly_trait_pred()
                        .map(|poly_trait_predicate| poly_trait_predicate)
                        .and_then(|poly_trait_predicate| poly_trait_predicate.no_bound_vars())
                        .and_then(|trait_predicate| {
                            trait_predicate.path_to(s, self.clone(), param_env)
                        })
                        .map(|path| (apred, path))
                }) else {
                    supposely_unreachable_fatal!(s, "ImplExprPredNotFound"; {
                        self, nested, predicates, trait_ref
                    })
                };
                use rustc_middle::ty::ToPolyTraitRef;
                let r#trait = apred
                    .predicate
                    .to_opt_poly_trait_pred()
                    .s_unwrap(s)
                    .to_poly_trait_ref()
                    .sinto(s);
                let path = path.sinto(s);
                if apred.is_extra_self_predicate {
                    ImplExprAtom::SelfImpl { r#trait, path }
                        .with_args(impl_exprs(s, &nested), trait_ref)
                } else {
                    ImplExprAtom::LocalBound {
                        clause_id: clause_id_of_predicate(s, apred.predicate),
                        r#trait,
                        path,
                    }
                    .with_args(impl_exprs(s, &nested), trait_ref)
                }
            }
            // Happens when we use a function pointer as an object implementing
            // a trait like `FnMut`
            ImplSource::FnPointer(rustc_trait_selection::traits::ImplSourceFnPointerData {
                fn_ty,
                nested,
            }) => ImplExprAtom::FnPointer {
                fn_ty: fn_ty.sinto(s),
            }
            .with_args(impl_exprs(s, &nested), trait_ref),
            ImplSource::Closure(rustc_trait_selection::traits::ImplSourceClosureData {
                closure_def_id,
                substs,
                nested,
            }) => {
                let substs = substs.as_closure();
                let parent_substs = substs.parent_substs().sinto(s);
                let signature = Box::new(substs.sig().sinto(s));
                ImplExprAtom::Closure {
                    closure_def_id: closure_def_id.sinto(s),
                    parent_substs,
                    signature,
                }
                .with_args(impl_exprs(s, &nested), trait_ref)
            }
            ImplSource::Object(data) => ImplExprAtom::Dyn {
                r#trait: data.upcast_trait_ref.skip_binder().sinto(s),
            }
            .with_args(impl_exprs(s, &data.nested), trait_ref),
            ImplSource::Builtin(x) => ImplExprAtom::Builtin {
                r#trait: self.skip_binder().sinto(s),
            }
            .with_args(impl_exprs(s, &x.nested), trait_ref),
            x => ImplExprAtom::Todo(format!(
                "ImplExprAtom::Todo(see https://github.com/hacspec/hax/issues/381) {:#?}\n\n{:#?}",
                x, self
            ))
            .with_args(vec![], trait_ref),
        }
    }
}

#[tracing::instrument(level = "trace", skip(s))]
pub fn clause_id_of_predicate<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    predicate: rustc_middle::ty::Predicate<'tcx>,
) -> u64 {
    use deterministic_hash::DeterministicHasher;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DeterministicHasher::new(DefaultHasher::new());

    let binder = predicate.kind();
    if let rustc_middle::ty::PredicateKind::Clause(ck) = binder.skip_binder() {
        let bvs: Vec<BoundVariableKind> = binder.bound_vars().sinto(s);
        let ck: ClauseKind = ck.sinto(s);
        hasher.write_u8(0);
        bvs.hash(&mut hasher);
        ck.hash(&mut hasher);
    } else {
        hasher.write_u8(1);
        predicate.sinto(s).hash(&mut hasher);
    }
    hasher.finish()
}

#[tracing::instrument(level = "trace", skip(s))]
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
            "Cannot hanlde error `{:?}` selecting `{:?}`",
            error,
            trait_ref
        ),
    }
}

pub mod copy_paste_from_rustc {
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_infer::traits::{FulfillmentErrorCode, TraitEngineExt as _};
    use rustc_middle::traits::{CodegenObligationError, DefiningAnchor};
    use rustc_middle::ty::{self, TyCtxt};
    use rustc_trait_selection::traits::error_reporting::TypeErrCtxtExt;
    use rustc_trait_selection::traits::{
        Obligation, ObligationCause, SelectionContext, TraitEngine, TraitEngineExt, Unimplemented,
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
    ) -> Result<rustc_trait_selection::traits::Selection<'tcx>, CodegenObligationError> {
        // We expect the input to be fully normalized.
        debug_assert_eq!(
            trait_ref,
            tcx.normalize_erasing_regions(param_env, trait_ref)
        );

        // Do the initial selection for the obligation. This yields the
        // shallow result we are looking for -- that is, what specific impl.
        let infcx = tcx
            .infer_ctxt()
            .ignoring_regions()
            .with_opaque_type_inference(DefiningAnchor::Bubble)
            .build();
        //~^ HACK `Bubble` is required for
        // this test to pass: type-alias-impl-trait/assoc-projection-ice.rs
        let mut selcx = SelectionContext::new(&infcx);

        let obligation_cause = ObligationCause::dummy();
        let obligation = Obligation::new(tcx, obligation_cause, param_env, trait_ref);

        let selection = match selcx.select(&obligation) {
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
        let mut fulfill_cx = <dyn TraitEngine<'tcx>>::new(tcx);
        let impl_source = selection.map(|predicate| {
            fulfill_cx.register_predicate_obligation(&infcx, predicate.clone());
            predicate
        });

        // In principle, we only need to do this so long as `impl_source`
        // contains unbound type parameters. It could be a slight
        // optimization to stop iterating early.
        let errors = fulfill_cx.select_all_or_error(&infcx);
        if !errors.is_empty() {
            // `rustc_monomorphize::collector` assumes there are no type errors.
            // Cycle errors are the only post-monomorphization errors possible; emit them now so
            // `rustc_ty_utils::resolve_associated_item` doesn't return `None` post-monomorphization.
            for err in errors {
                if let FulfillmentErrorCode::CodeCycle(cycle) = err.code {
                    infcx.err_ctxt().report_overflow_obligation_cycle(&cycle);
                }
            }
            return Err(CodegenObligationError::FulfillmentError);
        }

        let impl_source = infcx.resolve_vars_if_possible(impl_source);
        let impl_source = infcx.tcx.erase_regions(impl_source);

        // Opaque types may have gotten their hidden types constrained, but we can ignore them safely
        // as they will get constrained elsewhere, too.
        // (ouz-a) This is required for `type-alias-impl-trait/assoc-projection-ice.rs` to pass
        let _ = infcx.take_opaque_types();

        Ok(impl_source)
    }
}
