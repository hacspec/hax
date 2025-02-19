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
    Body: IsBody + TypeMappable,
{
    let tcx = s.base().tcx;
    let def_kind = get_def_kind(tcx, def_id);
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

/// The combination of type generics and related predicates.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ParamEnv {
    /// Generic parameters of the item.
    pub generics: TyGenerics,
    /// Required predicates for the item (see `traits::utils::required_predicates`).
    pub predicates: GenericPredicates,
}

/// Imbues [`rustc_hir::def::DefKind`] with a lot of extra information.
/// Important: the `owner_id()` must be the id of this definition.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_hir::def::DefKind, state: S as s, where Body: IsBody + TypeMappable)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum FullDefKind<Body> {
    // Types
    /// Refers to the struct definition, [`DefKind::Ctor`] refers to its constructor if it exists.
    Struct {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(s.base().tcx.adt_def(s.owner_id()).sinto(s))]
        def: AdtDef,
    },
    Union {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(s.base().tcx.adt_def(s.owner_id()).sinto(s))]
        def: AdtDef,
    },
    Enum {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(s.base().tcx.adt_def(s.owner_id()).sinto(s))]
        def: AdtDef,
    },
    /// Type alias: `type Foo = Bar;`
    TyAlias {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
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
    /// Associated type: `trait MyTrait { type Assoc; }`
    AssocTy {
        #[value(s.base().tcx.parent(s.owner_id()).sinto(s))]
        parent: DefId,
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(normalized_implied_predicates(s, s.owner_id()))]
        implied_predicates: GenericPredicates,
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
    /// Opaque type, aka `impl Trait`.
    OpaqueTy,

    // Traits
    Trait {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(normalized_implied_predicates(s, s.owner_id()))]
        implied_predicates: GenericPredicates,
        /// The special `Self: Trait` clause.
        #[value({
            use ty::Upcast;
            let tcx = s.base().tcx;
            let pred: ty::TraitPredicate =
                crate::traits::self_predicate(tcx, s.owner_id())
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
        items: Vec<(AssocItem, Arc<FullDef<Body>>)>,
    },
    /// Trait alias: `trait IntIterator = Iterator<Item = i32>;`
    TraitAlias,
    #[custom_arm(
        // Returns `TraitImpl` or `InherentImpl`.
        RDefKind::Impl { .. } => get_impl_contents(s),
    )]
    TraitImpl {
        param_env: ParamEnv,
        /// The trait that is implemented by this impl block.
        trait_pred: TraitPredicate,
        /// The `ImplExpr`s required to satisfy the predicates on the trait declaration. E.g.:
        /// ```ignore
        /// trait Foo: Bar {}
        /// impl Foo for () {} // would supply an `ImplExpr` for `Self: Bar`.
        /// ```
        implied_impl_exprs: Vec<ImplExpr>,
        /// Associated items, in the order of the trait declaration. Includes defaulted items.
        items: Vec<ImplAssocItem<Body>>,
    },
    #[disable_mapping]
    InherentImpl {
        param_env: ParamEnv,
        /// The type to which this block applies.
        ty: Ty,
        /// Associated items, in definition order.
        items: Vec<(AssocItem, Arc<FullDef<Body>>)>,
    },

    // Functions
    Fn {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(s.base().tcx.codegen_fn_attrs(s.owner_id()).inline.sinto(s))]
        inline: InlineAttr,
        #[value(s.base().tcx.constness(s.owner_id()) == rustc_hir::Constness::Const)]
        is_const: bool,
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
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(s.base().tcx.associated_item(s.owner_id()).sinto(s))]
        associated_item: AssocItem,
        #[value(s.base().tcx.codegen_fn_attrs(s.owner_id()).inline.sinto(s))]
        inline: InlineAttr,
        #[value(s.base().tcx.constness(s.owner_id()) == rustc_hir::Constness::Const)]
        is_const: bool,
        #[value(get_method_sig(s).sinto(s))]
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
        #[value(s.base().tcx.constness(s.owner_id()) == rustc_hir::Constness::Const)]
        is_const: bool,
        #[value({
            let fun_type = s.base().tcx.type_of(s.owner_id()).instantiate_identity();
            let ty::TyKind::Closure(_, args) = fun_type.kind() else { unreachable!() };
            ClosureArgs::sfrom(s, s.owner_id(), args.as_closure())
        })]
        args: ClosureArgs,
    },

    // Constants
    Const {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(s.base().tcx.type_of(s.owner_id()).instantiate_identity().sinto(s))]
        ty: Ty,
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
    },
    /// Associated constant: `trait MyTrait { const ASSOC: usize; }`
    AssocConst {
        #[value(s.base().tcx.parent(s.owner_id()).sinto(s))]
        parent: DefId,
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        #[value(s.base().tcx.associated_item(s.owner_id()).sinto(s))]
        associated_item: AssocItem,
        #[value(s.base().tcx.type_of(s.owner_id()).instantiate_identity().sinto(s))]
        ty: Ty,
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
    },
    /// Anonymous constant, e.g. the `1 + 2` in `[u8; 1 + 2]`
    AnonConst,
    /// An inline constant, e.g. `const { 1 + 2 }`
    InlineConst,
    Static {
        #[value(get_param_env(s, s.owner_id()))]
        param_env: ParamEnv,
        /// Whether it's a `unsafe static`, `safe static` (inside extern only) or just a `static`.
        safety: Safety,
        /// Whether it's a `static mut` or just a `static`.
        mutability: Mutability,
        /// Whether it's an anonymous static generated for nested allocations.
        nested: bool,
        #[value(s.base().tcx.type_of(s.owner_id()).instantiate_identity().sinto(s))]
        ty: Ty,
        #[value(s.owner_id().as_local().map(|ldid| Body::body(ldid, s)))]
        body: Option<Body>,
    },

    // Crates and modules
    ExternCrate,
    Use,
    Mod {
        #[value(get_mod_children(s.base().tcx, s.owner_id()).sinto(s))]
        items: Vec<DefId>,
    },
    /// An `extern` block.
    ForeignMod {
        #[value(get_foreign_mod_children(s.base().tcx, s.owner_id()).sinto(s))]
        items: Vec<DefId>,
    },

    // Type-level parameters
    /// Type parameter: the `T` in `struct Vec<T> { ... }`
    TyParam,
    /// Constant generic parameter: `struct Foo<const N: usize> { ... }`
    ConstParam,
    /// Lifetime parameter: the `'a` in `struct Foo<'a> { ... }`
    LifetimeParam,

    // ADT parts
    /// Refers to the variant definition, [`DefKind::Ctor`] refers to its constructor if it exists.
    Variant,
    /// The constructor function of a tuple/unit struct or tuple/unit enum variant.
    #[custom_arm(RDefKind::Ctor(ctor_of, _) => get_ctor_contents(s, ctor_of.sinto(s)),)]
    Ctor {
        adt_def_id: DefId,
        ctor_of: CtorOf,
        variant_id: VariantIdx,
        fields: IndexVec<FieldIdx, FieldDef>,
        output_ty: Ty,
    },
    /// A field in a struct, enum or union. e.g.
    /// - `bar` in `struct Foo { bar: u8 }`
    /// - `Foo::Bar::0` in `enum Foo { Bar(u8) }`
    Field,

    // Others
    /// Macros
    Macro(MacroKind),
    /// A use of `global_asm!`.
    GlobalAsm,
    /// A synthetic coroutine body created by the lowering of a coroutine-closure, such as an async
    /// closure.
    SyntheticCoroutineBody,
}

/// An associated item in a trait impl. This can be an item provided by the trait impl, or an item
/// that reuses the trait decl default value.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct ImplAssocItem<Body> {
    pub name: Symbol,
    /// The definition of the item from the trait declaration. This is `AssocTy`, `AssocFn` or
    /// `AssocConst`.
    pub decl_def: Arc<FullDef<Body>>,
    /// The `ImplExpr`s required to satisfy the predicates on the associated type. E.g.:
    /// ```ignore
    /// trait Foo {
    ///     type Type<T>: Clone,
    /// }
    /// impl Foo for () {
    ///     type Type<T>: Arc<T>; // would supply an `ImplExpr` for `Arc<T>: Clone`.
    /// }
    /// ```
    /// Empty if this item is an associated const or fn.
    pub required_impl_exprs: Vec<ImplExpr>,
    /// The value of the implemented item.
    pub value: ImplAssocItemValue<Body>,
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum ImplAssocItemValue<Body> {
    /// The item is provided by the trait impl.
    Provided {
        /// The definition of the item in the trait impl. This is `AssocTy`, `AssocFn` or
        /// `AssocConst`.
        def: Arc<FullDef<Body>>,
        /// Whether the trait had a default value for this item (which is therefore overriden).
        is_override: bool,
    },
    /// This is an associated type that reuses the trait declaration default.
    DefaultedTy {
        /// The default type, with generics properly instantiated. Note that this can be a GAT;
        /// relevant generics and predicates can be found in `decl_def`.
        ty: Ty,
    },
    /// This is a non-overriden default method.
    /// FIXME: provide properly instantiated generics.
    DefaultedFn {},
    /// This is an associated const that reuses the trait declaration default. The default const
    /// value can be found in `decl_def`.
    DefaultedConst,
}

impl<Body> FullDef<Body> {
    #[cfg(feature = "rustc")]
    pub fn rust_def_id(&self) -> RDefId {
        (&self.def_id).into()
    }

    pub fn kind(&self) -> &FullDefKind<Body> {
        &self.kind
    }

    /// Returns the generics and predicates for definitions that have those.
    pub fn param_env(&self) -> Option<&ParamEnv> {
        use FullDefKind::*;
        match &self.kind {
            Struct { param_env, .. }
            | Union { param_env, .. }
            | Enum { param_env, .. }
            | Trait { param_env, .. }
            | TyAlias { param_env, .. }
            | AssocTy { param_env, .. }
            | Fn { param_env, .. }
            | AssocFn { param_env, .. }
            | Const { param_env, .. }
            | AssocConst { param_env, .. }
            | Static { param_env, .. }
            | TraitImpl { param_env, .. }
            | InherentImpl { param_env, .. } => Some(param_env),
            _ => None,
        }
    }
}

impl<Body> ImplAssocItem<Body> {
    /// The relevant definition: the provided implementation if any, otherwise the default
    /// declaration from the trait declaration.
    pub fn def(&self) -> &FullDef<Body> {
        match &self.value {
            ImplAssocItemValue::Provided { def, .. } => def.as_ref(),
            _ => self.decl_def.as_ref(),
        }
    }

    /// The kind of item this is.
    pub fn assoc_kind(&self) -> AssocKind {
        match self.def().kind() {
            FullDefKind::AssocTy { .. } => AssocKind::Type,
            FullDefKind::AssocFn { .. } => AssocKind::Fn,
            FullDefKind::AssocConst { .. } => AssocKind::Const,
            _ => unreachable!(),
        }
    }
}

/// Gets the kind of the definition.
#[cfg(feature = "rustc")]
pub fn get_def_kind<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> RDefKind {
    if def_id == rustc_span::def_id::CRATE_DEF_ID.to_def_id() {
        // Horrible hack: without this, `def_kind` crashes on the crate root. Presumably some table
        // isn't properly initialized otherwise.
        let _ = tcx.def_span(def_id);
    };
    tcx.def_kind(def_id)
}

/// Gets the attributes of the definition.
#[cfg(feature = "rustc")]
pub fn get_def_span<'tcx>(
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

/// Gets the children of a module.
#[cfg(feature = "rustc")]
fn get_mod_children<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> Vec<RDefId> {
    match def_id.as_local() {
        Some(ldid) => match tcx.hir_node_by_def_id(ldid) {
            rustc_hir::Node::Crate(m)
            | rustc_hir::Node::Item(&rustc_hir::Item {
                kind: rustc_hir::ItemKind::Mod(m),
                ..
            }) => m
                .item_ids
                .iter()
                .map(|item_id| item_id.owner_id.to_def_id())
                .collect(),
            node => panic!("DefKind::Module is an unexpected node: {node:?}"),
        },
        None => tcx
            .module_children(def_id)
            .iter()
            .map(|child| child.res.def_id())
            .collect(),
    }
}

/// Gets the children of an `extern` block. Empty if the block is not defined in the current crate.
#[cfg(feature = "rustc")]
fn get_foreign_mod_children<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> Vec<RDefId> {
    match def_id.as_local() {
        Some(ldid) => tcx
            .hir_node_by_def_id(ldid)
            .expect_item()
            .expect_foreign_mod()
            .1
            .iter()
            .map(|foreign_item_ref| foreign_item_ref.id.owner_id.to_def_id())
            .collect(),
        None => vec![],
    }
}

#[cfg(feature = "rustc")]
fn get_impl_contents<'tcx, S, Body>(s: &S) -> FullDefKind<Body>
where
    S: UnderOwnerState<'tcx>,
    Body: IsBody + TypeMappable,
{
    use std::collections::HashMap;
    let tcx = s.base().tcx;
    let impl_def_id = s.owner_id();
    let param_env = get_param_env(s, impl_def_id);
    match tcx.impl_subject(impl_def_id).instantiate_identity() {
        ty::ImplSubject::Inherent(ty) => {
            let items = tcx
                .associated_items(impl_def_id)
                .in_definition_order()
                .map(|assoc| (assoc, assoc.def_id))
                .collect::<Vec<_>>()
                .sinto(s);
            FullDefKind::InherentImpl {
                param_env,
                ty: ty.sinto(s),
                items,
            }
        }
        ty::ImplSubject::Trait(trait_ref) => {
            // Also record the polarity.
            let polarity = tcx.impl_polarity(impl_def_id);
            let trait_pred = TraitPredicate {
                trait_ref: trait_ref.sinto(s),
                is_positive: matches!(polarity, ty::ImplPolarity::Positive),
            };
            // Impl exprs required by the trait.
            let required_impl_exprs =
                solve_item_implied_traits(s, trait_ref.def_id, trait_ref.args);

            let mut item_map: HashMap<RDefId, _> = tcx
                .associated_items(impl_def_id)
                .in_definition_order()
                .map(|assoc| (assoc.trait_item_def_id.unwrap(), assoc))
                .collect();
            let items = tcx
                .associated_items(trait_ref.def_id)
                .in_definition_order()
                .map(|decl_assoc| {
                    let decl_def_id = decl_assoc.def_id;
                    let decl_def = decl_def_id.sinto(s);
                    // Impl exprs required by the item.
                    let required_impl_exprs;
                    let value = match item_map.remove(&decl_def_id) {
                        Some(impl_assoc) => {
                            required_impl_exprs = {
                                let item_args =
                                    ty::GenericArgs::identity_for_item(tcx, impl_assoc.def_id);
                                // Subtlety: we have to add the GAT arguments (if any) to the trait ref arguments.
                                let args = item_args.rebase_onto(tcx, impl_def_id, trait_ref.args);
                                let state_with_id =
                                    with_owner_id(s.base(), (), (), impl_assoc.def_id);
                                solve_item_implied_traits(&state_with_id, decl_def_id, args)
                            };

                            ImplAssocItemValue::Provided {
                                def: impl_assoc.def_id.sinto(s),
                                is_override: decl_assoc.defaultness(tcx).has_value(),
                            }
                        }
                        None => {
                            required_impl_exprs = if tcx.generics_of(decl_def_id).is_own_empty() {
                                // Non-GAT case.
                                let item_args =
                                    ty::GenericArgs::identity_for_item(tcx, decl_def_id);
                                let args = item_args.rebase_onto(tcx, impl_def_id, trait_ref.args);
                                let state_with_id = with_owner_id(s.base(), (), (), impl_def_id);
                                solve_item_implied_traits(&state_with_id, decl_def_id, args)
                            } else {
                                // FIXME: For GATs, we need a param_env that has the arguments of
                                // the impl plus those of the associated type, but there's no
                                // def_id with that param_env.
                                vec![]
                            };
                            match decl_assoc.kind {
                                ty::AssocKind::Type => {
                                    let ty = tcx
                                        .type_of(decl_def_id)
                                        .instantiate(tcx, trait_ref.args)
                                        .sinto(s);
                                    ImplAssocItemValue::DefaultedTy { ty }
                                }
                                ty::AssocKind::Fn => ImplAssocItemValue::DefaultedFn {},
                                ty::AssocKind::Const => ImplAssocItemValue::DefaultedConst {},
                            }
                        }
                    };

                    ImplAssocItem {
                        name: decl_assoc.name.sinto(s),
                        value,
                        required_impl_exprs,
                        decl_def,
                    }
                })
                .collect();
            assert!(item_map.is_empty());
            FullDefKind::TraitImpl {
                param_env,
                trait_pred,
                implied_impl_exprs: required_impl_exprs,
                items,
            }
        }
    }
}

/// The signature of a method impl may be a subtype of the one expected from the trait decl, as in
/// the example below. For correctness, we must be able to map from the method generics declared in
/// the trait to the actual method generics. Because this would require type inference, we instead
/// simply return the declared signature. This will cause issues if it is possible to use such a
/// more-specific implementation with its more-specific type, but we have a few other issues with
/// lifetime-generic function pointers anyway so this is unlikely to cause problems.
///
/// ```ignore
/// trait MyCompare<Other>: Sized {
///     fn compare(self, other: Other) -> bool;
/// }
/// impl<'a> MyCompare<&'a ()> for &'a () {
///     // This implementation is more general because it works for non-`'a` refs. Note that only
///     // late-bound vars may differ in this way.
///     // `<&'a () as MyCompare<&'a ()>>::compare` has type `fn<'b>(&'a (), &'b ()) -> bool`,
///     // but type `fn(&'a (), &'a ()) -> bool` was expected from the trait declaration.
///     fn compare<'b>(self, _other: &'b ()) -> bool {
///         true
///     }
/// }
/// ```
#[cfg(feature = "rustc")]
fn get_method_sig<'tcx, S>(s: &S) -> ty::PolyFnSig<'tcx>
where
    S: UnderOwnerState<'tcx>,
{
    let tcx = s.base().tcx;
    let def_id = s.owner_id();
    let real_sig = tcx.fn_sig(def_id).instantiate_identity();
    let item = tcx.associated_item(def_id);
    if !matches!(item.container, ty::AssocItemContainer::ImplContainer) {
        return real_sig;
    }
    let Some(decl_method_id) = item.trait_item_def_id else {
        return real_sig;
    };
    let declared_sig = tcx.fn_sig(decl_method_id);

    // TODO(Nadrieril): Temporary hack: if the signatures have the same number of bound vars, we
    // keep the real signature. While the declared signature is more correct, it is also less
    // normalized and we can't normalize without erasing regions but regions are crucial in
    // function signatures. Hence we cheat here, until charon gains proper normalization
    // capabilities.
    if declared_sig.skip_binder().bound_vars().len() == real_sig.bound_vars().len() {
        return real_sig;
    }

    let impl_def_id = item.container_id(tcx);
    // The trait predicate that is implemented by the surrounding impl block.
    let implemented_trait_ref = tcx
        .impl_trait_ref(impl_def_id)
        .unwrap()
        .instantiate_identity();
    // Construct arguments for the declared method generics in the context of the implemented
    // method generics.
    let impl_args = ty::GenericArgs::identity_for_item(tcx, def_id);
    let decl_args = impl_args.rebase_onto(tcx, impl_def_id, implemented_trait_ref.args);
    let sig = declared_sig.instantiate(tcx, decl_args);
    // Avoids accidentally using the same lifetime name twice in the same scope
    // (once in impl parameters, second in the method declaration late-bound vars).
    let sig = tcx.anonymize_bound_vars(sig);
    sig
}

#[cfg(feature = "rustc")]
fn get_ctor_contents<'tcx, S, Body>(s: &S, ctor_of: CtorOf) -> FullDefKind<Body>
where
    S: UnderOwnerState<'tcx>,
    Body: IsBody + TypeMappable,
{
    let tcx = s.base().tcx;
    let def_id = s.owner_id();

    // The def_id of the adt this ctor belongs to.
    let adt_def_id = match ctor_of {
        CtorOf::Struct => tcx.parent(def_id),
        CtorOf::Variant => tcx.parent(tcx.parent(def_id)),
    };
    let adt_def = tcx.adt_def(adt_def_id);
    let variant_id = adt_def.variant_index_with_ctor_id(def_id);
    let fields = adt_def.variant(variant_id).fields.sinto(s);
    let generic_args = ty::GenericArgs::identity_for_item(tcx, adt_def_id);
    let output_ty = ty::Ty::new_adt(tcx, adt_def, generic_args).sinto(s);
    FullDefKind::Ctor {
        adt_def_id: adt_def_id.sinto(s),
        ctor_of,
        variant_id: variant_id.sinto(s),
        fields,
        output_ty,
    }
}

/// This normalizes trait clauses before calling `sinto` on them. This is a bit of a hack required
/// by charon for now. We can't normalize all clauses as this would lose region information in
/// outlives clauses.
/// TODO: clarify normalization in charon (https://github.com/AeneasVerif/charon/issues/300).
#[cfg(feature = "rustc")]
fn normalize_trait_clauses<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    predicates: ty::GenericPredicates<'tcx>,
) -> GenericPredicates {
    let clauses: Vec<_> = predicates
        .predicates
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
            (clause, *span)
        })
        .collect();
    GenericPredicates {
        predicates: clauses.sinto(s),
    }
}

/// Get the `required_predicates` for the given `def_id` and process them with
/// `normalize_trait_clauses`.
#[cfg(feature = "rustc")]
fn normalized_required_predicates<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
) -> GenericPredicates {
    let tcx = s.base().tcx;
    normalize_trait_clauses(s, required_predicates(tcx, def_id))
}

/// Get the `implied_predicates` for the given `def_id` and process them with
/// `normalize_trait_clauses`.
#[cfg(feature = "rustc")]
fn normalized_implied_predicates<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
) -> GenericPredicates {
    let tcx = s.base().tcx;
    normalize_trait_clauses(s, implied_predicates(tcx, def_id))
}

#[cfg(feature = "rustc")]
fn get_param_env<'tcx, S: BaseState<'tcx>>(s: &S, def_id: RDefId) -> ParamEnv {
    let tcx = s.base().tcx;
    let s = &with_owner_id(s.base(), (), (), def_id);
    ParamEnv {
        generics: tcx.generics_of(def_id).sinto(s),
        predicates: normalized_required_predicates(s, def_id),
    }
}
