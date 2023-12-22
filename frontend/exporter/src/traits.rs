use crate::prelude::*;

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: search_clause::PathChunk<'tcx>, state: S as tcx)]
#[derive(
    Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
pub enum ImplExprPathChunk {
    AssocItem(AssocItem, TraitPredicate),
    Parent(TraitPredicate),
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
        sig: Box<MirPolyFnSig>,
    },
    /// If failed to solve a trait ref
    Error(String),
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
        AssocItem(AssocItem, TraitPredicate<'tcx>),
        Parent(TraitPredicate<'tcx>),
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
        s: &S,
    ) -> bool {
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
        fn parents_trait_predicates(self, s: &S) -> Vec<TraitPredicate<'tcx>> {
            let tcx = s.base().tcx;
            let predicates = tcx
                .predicates_defined_on_or_above(self.def_id())
                .into_iter()
                .map(|(predicate, _)| predicate);
            predicates_to_trait_predicates(tcx, predicates, self.trait_ref.substs).collect()
        }
        fn associated_items_trait_predicates(
            self,
            s: &S,
        ) -> Vec<(AssocItem, subst::EarlyBinder<Vec<TraitPredicate<'tcx>>>)> {
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
            if predicate_equality(self.to_predicate(tcx), target.to_predicate(tcx), s) {
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
                .filter_map(|p| recurse(p).map(|path| cons(PathChunk::Parent(p), path)))
                .max_by_key(|path| path.len())
                .or_else(|| {
                    self.associated_items_trait_predicates(s)
                        .into_iter()
                        .filter_map(|(item, binder)| {
                            binder.skip_binder().into_iter().find_map(|p| {
                                recurse(p).map(|path| cons(PathChunk::AssocItem(item, p), path))
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
        assert!(self.bound_vars().is_empty());
        let trait_ref: Binder<TraitRef> = self.sinto(s);
        let trait_ref = trait_ref.value;

        let Some(impl_source) = select_trait_candidate(s, param_env, *self) else {
            return ImplExprAtom::Todo(format!("impl_expr failed on {:#?}", self))
                .with_args(vec![], trait_ref);
        };
        match impl_source {
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
                let Some((predicate, path)) = predicates.into_iter().find_map(|(predicate, _)| {
                    predicate
                        .to_opt_poly_trait_pred()
                        .map(|poly_trait_predicate| poly_trait_predicate)
                        .and_then(|poly_trait_predicate| poly_trait_predicate.no_bound_vars())
                        .and_then(|trait_predicate| {
                            trait_predicate.path_to(s, self.clone(), param_env)
                        })
                        .map(|path| (predicate, path))
                }) else {
                    return ImplExprAtom::Todo(format!("implsource::param \n\n{:#?}", self))
                        .with_args(impl_exprs(s, &nested), trait_ref);
                };
                let clause_id: u64 = clause_id_of_predicate(*predicate);
                use rustc_middle::ty::ToPolyTraitRef;
                let r#trait = predicate
                    .to_opt_poly_trait_pred()
                    .s_unwrap(s)
                    .to_poly_trait_ref()
                    .sinto(s);
                ImplExprAtom::LocalBound {
                    clause_id,
                    r#trait,
                    path: path.sinto(s),
                }
                .with_args(impl_exprs(s, &nested), trait_ref)
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
                let sig = Box::new(substs.sig().sinto(s));
                ImplExprAtom::Closure {
                    closure_def_id: closure_def_id.sinto(s),
                    parent_substs,
                    sig,
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
            x => {
                ImplExprAtom::Todo(format!("{:#?}\n\n{:#?}", x, self)).with_args(vec![], trait_ref)
            }
        }
    }
}

pub fn clause_id_of_predicate(predicate: rustc_middle::ty::Predicate) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    // TODO: use stable hash here?
    let mut s = DefaultHasher::new();
    predicate.hash(&mut s);
    s.finish()
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
///
/// TODO: returns an Option for now, `None` means we hit the indexing
/// bug (see <https://github.com/rust-lang/rust/issues/112242>).
#[tracing::instrument(level = "trace", skip(s))]
pub fn select_trait_candidate<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    param_env: rustc_middle::ty::ParamEnv<'tcx>,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> Option<rustc_trait_selection::traits::Selection<'tcx>> {
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_trait_selection::traits::{Obligation, ObligationCause, SelectionContext};
    let tcx = s.base().tcx;
    let trait_ref = tcx
        .try_normalize_erasing_regions(param_env, trait_ref)
        .unwrap_or(trait_ref);

    // Do the initial selection for the obligation. This yields the
    // shallow result we are looking for -- that is, what specific impl.
    let infcx = tcx.infer_ctxt().ignoring_regions().build();
    let mut selcx = SelectionContext::new(&infcx);

    let obligation_cause = ObligationCause::dummy();
    let obligation = Obligation::new(tcx, obligation_cause, param_env, trait_ref);

    let selection = {
        use std::panic;
        panic::set_hook(Box::new(|_info| {}));
        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| selcx.select(&obligation)));
        let _ = panic::take_hook();
        result
    };
    match selection {
        Ok(Ok(Some(selection))) => Some(infcx.resolve_vars_if_possible(selection)),
        Ok(error) => fatal!(
            s,
            "Cannot hanlde error `{:?}` selecting `{:?}`",
            error,
            trait_ref
        ),
        Err(_) => None,
    }
}
