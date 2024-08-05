use crate::prelude::*;

#[cfg(feature = "rustc")]
use rustc_middle::ty;
#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;

/// Gathers a lot of definition information about a [`rustc_hir::def_id::DefId`].
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::def_id::DefId, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FullDef {
    #[value(self.sinto(s))]
    pub def_id: DefId,
    #[value(s.base().tcx.opt_parent(*self).sinto(s))]
    pub parent: Option<DefId>,
    #[value(s.base().tcx.def_span(*self).sinto(s))]
    pub span: Span,
    #[value(s.base().tcx.def_key(*self).disambiguated_data.sinto(s))]
    pub path_item: DisambiguatedDefPathItem,
    #[value({
        let state_with_id = State { thir: (), mir: (), owner_id: *self, base: s.base() };
        s.base().tcx.def_kind(*self).sinto(&state_with_id)
    })]
    pub kind: FullDefKind,
}

/// Imbues [`rustc_hir::def::DefKind`] with a lot of extra information.
/// Important: the `owner_id()` must be the id of this definition.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::def::DefKind, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum FullDefKind {
    // Type namespace
    Mod,
    /// Refers to the struct definition, [`DefKind::Ctor`] refers to its constructor if it exists.
    Struct {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.adt_def(s.owner_id()).sinto(s))]
        def: AdtDef,
    },
    Union {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.adt_def(s.owner_id()).sinto(s))]
        def: AdtDef,
    },
    Enum {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.adt_def(s.owner_id()).sinto(s))]
        def: AdtDef,
    },
    /// Refers to the variant definition, [`DefKind::Ctor`] refers to its constructor if it exists.
    Variant,
    Trait {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        // `predicates_of` has the special `Self: Trait` clause as its last element.
        #[value({
            let (clause, _) = s.base().tcx.predicates_of(s.owner_id()).predicates.last().unwrap();
            let Some(ty::ClauseKind::Trait(trait_ref)) = clause.kind().no_bound_vars() else {
                panic!()
            };
            trait_ref.sinto(s)
        })]
        self_predicate: TraitPredicate,
        /// Associated items, in definition order.
        #[value(s.base().tcx.associated_items(s.owner_id()).in_definition_order().collect::<Vec<_>>().sinto(s))]
        items: Vec<AssocItem>,
    },
    /// Type alias: `type Foo = Bar;`
    TyAlias {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        /// `Some` if the item is in the local crate.
        #[value(s.base().tcx.hir().get_if_local(s.owner_id()).map(|node| {
            let rustc_hir::Node::Item(item) = node else { unreachable!() };
            let rustc_hir::ItemKind::TyAlias(ty, _generics) = &item.kind else { unreachable!() };
            ty.sinto(s)
        }))]
        ty: Option<Ty>,
    },
    /// Type from an `extern` block.
    ForeignTy,
    /// Trait alias: `trait IntIterator = Iterator<Item = i32>;`
    TraitAlias,
    /// Associated type: `trait MyTrait { type Assoc; }`
    AssocTy {
        #[value(s.base().tcx.parent(s.owner_id()).sinto(s))]
        parent: DefId,
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_item_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.associated_item(s.owner_id()).sinto(s))]
        associated_item: AssocItem,
        #[value({
            let tcx = s.base().tcx;
            if tcx.defaultness(s.owner_id()).has_value() {
                Some(tcx.type_of(s.owner_id()).instantiate_identity().sinto(s))
            } else {
                None
            }
        })]
        value: Option<Ty>,
    },
    /// Type parameter: the `T` in `struct Vec<T> { ... }`
    TyParam,

    // Value namespace
    Fn {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.fn_sig(s.owner_id()).instantiate_identity().sinto(s))]
        sig: PolyFnSig,
    },
    /// Associated function: `impl MyStruct { fn associated() {} }` or `trait Foo { fn associated()
    /// {} }`
    AssocFn {
        #[value(s.base().tcx.parent(s.owner_id()).sinto(s))]
        parent: DefId,
        #[value(s.base().tcx.associated_item(s.owner_id()).sinto(s))]
        associated_item: AssocItem,
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.fn_sig(s.owner_id()).instantiate_identity().sinto(s))]
        sig: PolyFnSig,
    },
    /// A closure, coroutine, or coroutine-closure.
    ///
    /// Note: the (early-bound) generics of a closure are the same as those of the item in which it
    /// is defined.
    Closure {
        /// The enclosing item. Note: this item could itself be a closure; to get the generics, you
        /// might have to recurse through several layers of parents until you find a function or
        /// constant.
        #[value(s.base().tcx.parent(s.owner_id()).sinto(s))]
        parent: DefId,
        #[value({
            let fun_type = s.base().tcx.type_of(s.owner_id()).instantiate_identity();
            match fun_type.kind() {
                ty::TyKind::Closure(_, args) => args.as_closure().sinto(s),
                _ => unreachable!(),
            }
        })]
        args: ClosureArgs,
    },
    Const {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.type_of(s.owner_id()).instantiate_identity().sinto(s))]
        ty: Ty,
    },
    /// Associated constant: `trait MyTrait { const ASSOC: usize; }`
    AssocConst {
        #[value(s.base().tcx.parent(s.owner_id()).sinto(s))]
        parent: DefId,
        #[value(s.base().tcx.associated_item(s.owner_id()).sinto(s))]
        associated_item: AssocItem,
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.type_of(s.owner_id()).instantiate_identity().sinto(s))]
        ty: Ty,
    },
    Static {
        /// Whether it's a `unsafe static`, `safe static` (inside extern only) or just a `static`.
        safety: Safety,
        /// Whether it's a `static mut` or just a `static`.
        mutability: Mutability,
        /// Whether it's an anonymous static generated for nested allocations.
        nested: bool,
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.type_of(s.owner_id()).instantiate_identity().sinto(s))]
        ty: Ty,
    },
    /// Constant generic parameter: `struct Foo<const N: usize> { ... }`
    ConstParam,
    /// Refers to the struct or enum variant's constructor.
    Ctor(CtorOf, CtorKind),

    // Macro namespace
    Macro(MacroKind),

    // Not namespaced (or they are, but we don't treat them so)
    ExternCrate,
    Use,
    /// An `extern` block.
    ForeignMod,
    /// Anonymous constant, e.g. the `1 + 2` in `[u8; 1 + 2]`
    AnonConst,
    /// An inline constant, e.g. `const { 1 + 2 }`
    InlineConst,
    /// Opaque type, aka `impl Trait`.
    OpaqueTy,
    Impl {
        #[value(s.base().tcx.generics_of(s.owner_id()).sinto(s))]
        generics: TyGenerics,
        #[value(get_generic_predicates(s, s.owner_id()))]
        predicates: GenericPredicates,
        #[value(s.base().tcx.impl_subject(s.owner_id()).instantiate_identity().sinto(s))]
        impl_subject: ImplSubject,
        /// Associated items, in definition order.
        #[value(s.base().tcx.associated_items(s.owner_id()).in_definition_order().collect::<Vec<_>>().sinto(s))]
        items: Vec<AssocItem>,
    },
    /// A field in a struct, enum or union. e.g.
    /// - `bar` in `struct Foo { bar: u8 }`
    /// - `Foo::Bar::0` in `enum Foo { Bar(u8) }`
    Field,
    /// Lifetime parameter: the `'a` in `struct Foo<'a> { ... }`
    LifetimeParam,
    /// A use of `global_asm!`.
    GlobalAsm,
}

impl FullDef {
    pub fn kind(&self) -> &FullDefKind {
        &self.kind
    }
    pub fn generics(&self) -> Option<(&TyGenerics, &GenericPredicates)> {
        use FullDefKind::*;
        match &self.kind {
            Struct {
                generics,
                predicates,
                ..
            }
            | Union {
                generics,
                predicates,
                ..
            }
            | Enum {
                generics,
                predicates,
                ..
            }
            | Trait {
                generics,
                predicates,
                ..
            }
            | TyAlias {
                generics,
                predicates,
                ..
            }
            | AssocTy {
                generics,
                predicates,
                ..
            }
            | Fn {
                generics,
                predicates,
                ..
            }
            | AssocFn {
                generics,
                predicates,
                ..
            }
            | Const {
                generics,
                predicates,
                ..
            }
            | AssocConst {
                generics,
                predicates,
                ..
            }
            | Static {
                generics,
                predicates,
                ..
            }
            | Impl {
                generics,
                predicates,
                ..
            } => Some((generics, predicates)),
            _ => None,
        }
    }
}

#[cfg(feature = "rustc")]
fn process_generic_predicates<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    predicates: &[(ty::Clause<'tcx>, rustc_span::Span)],
) -> Vec<(Predicate, Span)> {
    // Normalize trait predicates because charon needs it.
    // TODO: stop doing that.
    let mut predicates: Vec<_> = predicates
        .iter()
        .map(|(clause, span)| {
            let mut clause = clause.clone();
            if matches!(&clause.kind().skip_binder(), ty::ClauseKind::Trait(_)) {
                clause = s
                    .base()
                    .tcx
                    .normalize_erasing_regions(s.param_env(), clause);
            }
            (clause.as_predicate(), *span)
        })
        .collect();
    // Sort trait predicates first because charon needs it.
    // TODO: stop doing that.
    predicates.sort_by_key(|(pred, _)| {
        !matches!(
            &pred.kind().skip_binder(),
            ty::PredicateKind::Clause(ty::ClauseKind::Trait(_))
        )
    });
    predicates.sinto(s)
}

#[cfg(feature = "rustc")]
fn get_generic_predicates<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
) -> GenericPredicates {
    // We use `predicates_defined_on` to skip the implied `Self` clause.
    let predicates = s.base().tcx.predicates_defined_on(def_id);
    let pred_list = process_generic_predicates(s, predicates.predicates);
    GenericPredicates {
        parent: predicates.parent.sinto(s),
        predicates: pred_list,
    }
}

#[cfg(feature = "rustc")]
fn get_item_predicates<'tcx, S: UnderOwnerState<'tcx>>(s: &S, def_id: RDefId) -> GenericPredicates {
    let tcx = s.base().tcx;
    let parent_id = tcx.parent(def_id);
    // `item_bounds` cannot be called on a trait impl item, and returns empty on an inherent impl
    // item. So we only call it for trait decl items.
    let predicates = match tcx.def_kind(parent_id) {
        rustc_hir::def::DefKind::Trait => {
            // TODO: we probably want to use `explicit_item_bounds` instead, but should do so
            // consistently.
            let clauses = tcx.item_bounds(def_id).instantiate_identity();
            use crate::rustc_middle::query::Key;
            let span = clauses.default_span(tcx);
            clauses.iter().map(|c| (c, span)).collect::<Vec<_>>()
        }
        _ => Vec::new(),
    };
    let predicates = process_generic_predicates(s, predicates.as_slice());
    GenericPredicates {
        parent: Some(parent_id.sinto(s)),
        predicates,
    }
}
