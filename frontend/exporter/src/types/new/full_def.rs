use crate::prelude::*;
use std::sync::Arc;

#[cfg(feature = "rustc")]
use rustc_hir::def::DefKind as RDefKind;
#[cfg(feature = "rustc")]
use rustc_middle::ty;
#[cfg(feature = "rustc")]
use rustc_span::def_id::DefId as RDefId;

/// Gathers a lot of definition information about a [`rustc_hir::def_id::DefId`].
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FullDef<Body = ()> {
    pub def_id: DefId,
    /// The enclosing item.
    pub parent: Option<DefId>,
    /// The span of the definition of this item (e.g. for a function this is is signature).
    pub span: Span,
    /// The span of the whole definition (including e.g. the function body).
    pub source_span: Option<Span>,
    /// The text of the whole definition.
    pub source_text: Option<String>,
    /// Attributes on this definition, if applicable.
    pub attributes: Vec<Attribute>,
    /// Visibility of the definition, for definitions where this makes sense.
    pub visibility: Option<bool>,
    /// If this definition is a lang item, we store the identifier, e.g. `sized`.
    pub lang_item: Option<String>,
    /// If this definition is a diagnostic item, we store the identifier, e.g. `box_new`.
    pub diagnostic_item: Option<String>,
    pub kind: FullDefKind<Body>,
}

#[cfg(feature = "rustc")]
fn translate_full_def<'tcx, S, Body>(s: &S, def_id: RDefId) -> FullDef<Body>
where
    S: BaseState<'tcx>,
    Body: IsBody,
{
    let tcx = s.base().tcx;
    let def_kind = tcx.def_kind(def_id);
    let kind = {
        let state_with_id = with_owner_id(s.base(), (), (), def_id);
        def_kind.sinto(&state_with_id)
    };

    let source_span = def_id.as_local().map(|ldid| tcx.source_span(ldid));
    let source_text = source_span
        .filter(|source_span| source_span.ctxt().is_root())
        .and_then(|source_span| tcx.sess.source_map().span_to_snippet(source_span).ok());

    FullDef {
        def_id: def_id.sinto(s),
        parent: tcx.opt_parent(def_id).sinto(s),
        span: get_def_span(tcx, def_id, def_kind).sinto(s),
        source_span: source_span.sinto(s),
        source_text,
        attributes: get_def_attrs(tcx, def_id, def_kind).sinto(s),
        visibility: get_def_visibility(tcx, def_id, def_kind),
        lang_item: s
            .base()
            .tcx
            .as_lang_item(def_id)
            .map(|litem| litem.name())
            .sinto(s),
        diagnostic_item: tcx.get_diagnostic_name(def_id).sinto(s),
        kind,
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S, Body> SInto<S, Arc<FullDef<Body>>> for RDefId
where
    Body: IsBody + TypeMappable,
    S: BaseState<'tcx>,
{
    fn sinto(&self, s: &S) -> Arc<FullDef<Body>> {
        if let Some(def) = s.with_item_cache(*self, |cache| cache.full_def.get().cloned()) {
            return def;
        }
        let def = Arc::new(translate_full_def(s, *self));
        s.with_item_cache(*self, |cache| cache.full_def.insert(def.clone()));
        def
    }
}

/// Imbues [`rustc_hir::def::DefKind`] with a lot of extra information.
/// Important: the `owner_id()` must be the id of this definition.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::def::DefKind, state: S as s, where Body: IsBody)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum FullDefKind<Body> {
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
        /// The special `Self: Trait` clause.
        #[value({
            use ty::Upcast;
            let tcx = s.base().tcx;
            let pred: ty::TraitPredicate =
                crate::traits::self_predicate(tcx, s.owner_id())
                    .unwrap()
                    .no_bound_vars()
                    .unwrap()
                    .upcast(tcx);
            pred.sinto(s)
        })]
        self_predicate: TraitPredicate,
        /// Associated items, in definition order.
        #[value(
            s
                .base()
                .tcx
                .associated_items(s.owner_id())
                .in_definition_order()
                .map(|assoc| (assoc, assoc.def_id))
                .collect::<Vec<_>>()
                .sinto(s)
        )]
        items: Vec<(AssocItem, Arc<FullDef>)>,
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
            let mut s = State::from_under_owner(s);
            s.base.ty_alias_mode = true;
            ty.sinto(&s)
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
        #[value(s.base().tcx.codegen_fn_attrs(s.owner_id()).inline.sinto(s))]
        inline: InlineAttr,
        #[value(s.base().tcx.fn_sig(s.owner_id()).instantiate_identity().sinto(s))]
        sig: PolyFnSig,
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
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
        #[value(s.base().tcx.codegen_fn_attrs(s.owner_id()).inline.sinto(s))]
        inline: InlineAttr,
        #[value(s.base().tcx.fn_sig(s.owner_id()).instantiate_identity().sinto(s))]
        sig: PolyFnSig,
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
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
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
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
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
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
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
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
        #[value(
            s
                .base()
                .tcx
                .associated_items(s.owner_id())
                .in_definition_order()
                .map(|assoc| (assoc, assoc.def_id))
                .collect::<Vec<_>>()
                .sinto(s)
        )]
        items: Vec<(AssocItem, Arc<FullDef>)>,
    },
    /// A field in a struct, enum or union. e.g.
    /// - `bar` in `struct Foo { bar: u8 }`
    /// - `Foo::Bar::0` in `enum Foo { Bar(u8) }`
    Field,
    /// Lifetime parameter: the `'a` in `struct Foo<'a> { ... }`
    LifetimeParam,
    /// A use of `global_asm!`.
    GlobalAsm,
    /// A synthetic coroutine body created by the lowering of a coroutine-closure, such as an async
    /// closure.
    SyntheticCoroutineBody,
}

impl<Body: IsBody> FullDef<Body> {
    #[cfg(feature = "rustc")]
    pub fn rust_def_id(&self) -> RDefId {
        (&self.def_id).into()
    }

    pub fn kind(&self) -> &FullDefKind<Body> {
        &self.kind
    }

    /// Returns the generics and predicates for definitions that have those.
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

/// Gets the attributes of the definition.
#[cfg(feature = "rustc")]
fn get_def_span<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    def_kind: RDefKind,
) -> rustc_span::Span {
    use RDefKind::*;
    match def_kind {
        // These kinds cause `def_span` to panic.
        ForeignMod => rustc_span::DUMMY_SP,
        _ => tcx.def_span(def_id),
    }
}

/// Gets the visibility (`pub` or not) of the definition. Returns `None` for defs that don't have a
/// meaningful visibility.
#[cfg(feature = "rustc")]
fn get_def_visibility<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    def_kind: RDefKind,
) -> Option<bool> {
    use RDefKind::*;
    match def_kind {
        AssocConst
        | AssocFn
        | Const
        | Enum
        | Field
        | Fn
        | ForeignTy
        | Macro { .. }
        | Mod
        | Static { .. }
        | Struct
        | Trait
        | TraitAlias
        | TyAlias { .. }
        | Union
        | Use
        | Variant => Some(tcx.visibility(def_id).is_public()),
        // These kinds don't have visibility modifiers (which would cause `visibility` to panic).
        AnonConst
        | AssocTy
        | Closure
        | ConstParam
        | Ctor { .. }
        | ExternCrate
        | ForeignMod
        | GlobalAsm
        | Impl { .. }
        | InlineConst
        | LifetimeParam
        | OpaqueTy
        | SyntheticCoroutineBody
        | TyParam => None,
    }
}

/// Gets the attributes of the definition.
#[cfg(feature = "rustc")]
fn get_def_attrs<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
    def_kind: RDefKind,
) -> &'tcx [rustc_ast::ast::Attribute] {
    use RDefKind::*;
    match def_kind {
        // These kinds cause `get_attrs_unchecked` to panic.
        ConstParam | LifetimeParam | TyParam | ForeignMod => &[],
        _ => tcx.get_attrs_unchecked(def_id),
    }
}

/// This normalizes trait clauses before calling `sinto` on them. This is a bit of a hack required
/// by charon for now. We can't normalize all clauses as this would lose region information in
/// outlives clauses.
/// TODO: clarify normalization in charon (https://github.com/AeneasVerif/charon/issues/300).
#[cfg(feature = "rustc")]
fn normalize_trait_clauses<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    predicates: &[(ty::Clause<'tcx>, rustc_span::Span)],
) -> Vec<(Predicate, Span)> {
    let predicates: Vec<_> = predicates
        .iter()
        .map(|(clause, span)| {
            let mut clause = *clause;
            if matches!(&clause.kind().skip_binder(), ty::ClauseKind::Trait(_)) {
                clause = s
                    .base()
                    .tcx
                    .try_normalize_erasing_regions(s.param_env(), clause)
                    .unwrap_or(clause);
            }
            (clause.as_predicate(), *span)
        })
        .collect();
    predicates.sinto(s)
}

/// Gets the `predicates_defined_on` the given `DefId` and processes them with
/// `normalize_trait_clauses`.
#[cfg(feature = "rustc")]
fn get_generic_predicates<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
) -> GenericPredicates {
    let predicates = predicates_defined_on(s.base().tcx, def_id);
    let pred_list = normalize_trait_clauses(s, predicates.predicates);
    GenericPredicates {
        parent: predicates.parent.sinto(s),
        predicates: pred_list,
    }
}

/// Gets the predicates defined on the given associated type and processes them with
/// `normalize_trait_clauses`.
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
    let predicates = normalize_trait_clauses(s, predicates.as_slice());
    GenericPredicates {
        parent: Some(parent_id.sinto(s)),
        predicates,
    }
}
