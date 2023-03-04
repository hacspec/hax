use crate::all;
use crate::all::*;
use crate::state::*;
use crate::{sinto_as_usize, sinto_todo, AdtInto, SInto};
use schemars::{schema_for, JsonSchema};
use serde::{Deserialize, Serialize};

use rustc_middle::ty::TyCtxt;

/// [FnDef] is a
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct FnDef {
    header: FnHeader,
    params: Vec<Param>,
    // c_variadic: bool,
    ret: Ty,
    body: Body,
    sig_span: Span,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::FnDecl<'tcx>, state: S as tcx)]
pub struct FnDecl {
    pub inputs: Vec<Ty>,
    pub output: FnRetTy,
    pub c_variadic: bool,
    pub implicit_self: ImplicitSelfKind,
    pub lifetime_elision_allowed: bool,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::FnSig<'tcx>, state: S as tcx)]
pub struct FnSig {
    pub header: FnHeader,
    pub decl: FnDecl,
    pub span: Span,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_hir::FnHeader, state: S as tcx)]
pub struct FnHeader {
    pub unsafety: Unsafety,
    pub constness: Constness,
    pub asyncness: IsAsync,
    pub abi: Abi,
}

pub type FnBody = all::Expr;

fn make_fn_def<'tcx, S: BaseState<'tcx>>(
    fn_sig: &rustc_hir::FnSig,
    body_id: &rustc_hir::BodyId,
    s: &S,
) -> FnDef {
    let (thir, params, body) = inspect_local_def_id(body_id.hir_id.owner.def_id, s);
    let ret = body.ty.clone();
    let s = State {
        tcx: s.tcx(),
        options: s.options(),
        thir: thir.clone(),
        def_id: (),
        opt_def_id: s.opt_def_id(),
        macro_infos: s.macro_infos(),
        local_ident_map: s.local_ident_map(),
    };
    FnDef {
        params,
        ret,
        body,
        sig_span: fn_sig.span.sinto(&s),
        header: fn_sig.header.sinto(&s),
    }
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, Body> for rustc_hir::BodyId {
    fn sinto(&self, s: &S) -> Body {
        inspect_local_def_id(s.tcx().hir().body_owner_def_id(self.clone()), s).2
    }
}

impl<'x, 'tcx, S: BaseState<'tcx> + HasDefId> SInto<S, Ty> for rustc_hir::Ty<'x> {
    fn sinto(self: &rustc_hir::Ty<'x>, s: &S) -> Ty {
        let ctx = rustc_hir_analysis::collect::ItemCtxt::new(s.tcx(), s.def_id());
        ctx.to_ty(self).sinto(s)
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::UseKind, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum UseKind {
    Single,
    Glob,
    ListStem,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::IsAuto, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum IsAuto {
    Yes,
    No,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::Defaultness, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Defaultness {
    Default { has_value: bool },
    Final,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::ImplPolarity, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ImplPolarity {
    Positive,
    Negative(Span),
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::Constness, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Constness {
    Const,
    NotConst,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::Generics<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub predicates: Vec<WherePredicate>,
    pub has_where_clause_predicates: bool,
    pub where_clause_span: Span,
    pub span: Span,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::WherePredicate<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum WherePredicate {
    BoundPredicate(WhereBoundPredicate),
    RegionPredicate(WhereRegionPredicate),
    EqPredicate(WhereEqPredicate),
}

impl<'tcx, S: BaseState<'tcx> + HasDefId> SInto<S, ImplItem> for rustc_hir::ImplItemRef {
    fn sinto(&self, s: &S) -> ImplItem {
        let tcx: rustc_middle::ty::TyCtxt = s.tcx();
        let impl_item = tcx.hir().impl_item(self.id.clone());
        impl_item.sinto(s)
    }
}

// #[derive(AdtInto)]
// #[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::ParamName, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ParamName {
    Plain(LocalIdent),
    Fresh,
    Error,
}
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::LifetimeParamKind, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum LifetimeParamKind {
    Explicit,
    Elided,
    Error,
}
#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::AnonConst, state: S as tcx)]
pub struct AnonConst {
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    pub body: Body,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::GenericParamKind<'tcx>, state: S as tcx)]
pub enum GenericParamKind {
    Lifetime {
        kind: LifetimeParamKind,
    },
    Type {
        #[map(x.map(|ty| ty.sinto(tcx)))]
        default: Option<Ty>,
        synthetic: bool,
    },
    Const {
        ty: Ty,
        default: Option<AnonConst>,
    },
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::GenericParam<'tcx>, state: S as tcx)]
pub struct GenericParam {
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    #[map(match x {
        rustc_hir::ParamName::Plain(loc_ident) =>
            ParamName::Plain(LocalIdent {
                name: loc_ident.as_str().to_string(),
                id: self.hir_id.sinto(tcx)
            }),
        rustc_hir::ParamName::Fresh =>
            ParamName::Fresh,
        rustc_hir::ParamName::Error =>
            ParamName::Error,
    })]
    pub name: ParamName,
    pub span: Span,
    pub pure_wrt_drop: bool,
    pub kind: GenericParamKind,
    pub colon_span: Option<Span>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::ImplItem<'tcx>, state: S as tcx)]
pub struct ImplItem {
    pub ident: Ident,
    pub owner_id: OwnerId,
    pub generics: Generics,
    pub kind: ImplItemKind,
    pub defaultness: Defaultness,
    pub span: Span,
    pub vis_span: Span,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::ImplItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ImplItemKind {
    Const(Ty, Body),
    #[custom_arm(rustc_hir::ImplItemKind::Fn(sig, body) => {
                ImplItemKind::Fn(make_fn_def(sig, body, tcx))
        },)]
    Fn(FnDef),
    Type(Ty),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::AssocItemKind, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum AssocItemKind {
    Const,
    Fn { has_self: bool },
    Type,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::Impl<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Impl {
    pub unsafety: Unsafety,
    pub polarity: ImplPolarity,
    pub defaultness: Defaultness,
    pub defaultness_span: Option<Span>,
    pub constness: Constness,
    pub generics: Generics,
    pub of_trait: Option<Path>,
    pub self_ty: Ty,
    pub items: Vec<ImplItem>,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::IsAsync, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum IsAsync {
    Async,
    NotAsync,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::FnRetTy<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum FnRetTy {
    DefaultReturn(Span),
    Return(Ty),
}

impl<'a, S> SInto<S, Path> for rustc_hir::TraitRef<'a> {
    fn sinto(&self, s: &S) -> Path {
        self.path
            .segments
            .iter()
            .map(|rustc_hir::PathSegment { ident, .. }| ident.as_str().into())
            .collect()
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::VariantData<'tcx>, state: S as tcx)]
pub enum VariantData {
    Struct(Vec<HirFieldDef>, bool),
    Tuple(Vec<HirFieldDef>, HirId, GlobalIdent),
    Unit(HirId, GlobalIdent),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::FieldDef<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct HirFieldDef {
    pub span: Span,
    pub vis_span: Span,
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    pub ty: Ty,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::Variant<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Variant {
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    pub data: VariantData,
    pub disr_expr: Option<AnonConst>,
    pub span: Span,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::ItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ItemKind {
    #[disable_mapping]
    MacroInvokation(MacroInvokation),
    ExternCrate(Option<Symbol>),
    Use(UsePath, UseKind),
    Static(Ty, Mutability, Body),
    Const(Ty, Body),
    // Fn(s: FnSig, g: Generics, body: FnBody),
    #[custom_arm(
            rustc_hir::ItemKind::Fn(sig, generics, body) => {
                ItemKind::Fn(generics.sinto(tcx), make_fn_def(sig, body, tcx))
            }
        )]
    Fn(Generics, FnDef),
    Macro(MacroDef, MacroKind),
    Mod(Vec<Item>),
    ForeignMod {
        abi: Abi,
        items: Vec<ForeignItem>,
    },
    GlobalAsm(InlineAsm),
    TyAlias(Ty, Generics),
    OpaqueTy(OpaqueTy),
    Enum(EnumDef, Generics),
    Struct(VariantData, Generics),
    Union(VariantData, Generics),
    Trait(IsAuto, Unsafety, Generics, GenericBounds, Vec<TraitItem>),
    TraitAlias(Generics, GenericBounds),
    Impl(Impl),
}

pub type EnumDef = Vec<Variant>;

// sinto_enum!(
//     {'tcx, S: BaseState<'tcx> + HasDefId} tcx: S as state,
//     #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
//     pub enum TraitFn (rustc_hir::TraitFn<'tcx>) {
//         Required(id: Vec<Ident>),
//         Provided(body: FnBody),
//     }
// );

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::TraitItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum TraitItemKind {
    Const(Ty, Option<Body>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Fn(sig, rustc_hir::TraitFn::Required(id)) => {
            TraitItemKind::RequiredFn(sig.sinto(tcx), id.sinto(tcx))
        }
    )]
    RequiredFn(FnSig, Vec<Ident>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Fn(sig, rustc_hir::TraitFn::Provided(body)) => {
            TraitItemKind::ProvidedFn(make_fn_def(sig, body, tcx))
        }
    )]
    ProvidedFn(FnDef),
    #[custom_arm(
        rustc_hir::TraitItemKind::Type(b, ty) => {
            TraitItemKind::Type(b.sinto(tcx), ty.map(|t| t.sinto(tcx)))
        }
    )]
    Type(GenericBounds, Option<Ty>),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::TraitItem<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitItem {
    pub ident: Ident,
    pub owner_id: OwnerId,
    pub generics: Generics,
    pub kind: TraitItemKind,
    pub span: Span,
    pub defaultness: Defaultness,
}

impl<'tcx, S: BaseState<'tcx> + HasDefId> SInto<S, Vec<Variant>> for rustc_hir::EnumDef<'tcx> {
    fn sinto(&self, s: &S) -> Vec<Variant> {
        self.variants.iter().map(|v| v.sinto(s)).collect()
    }
}

impl<'a, S: BaseState<'a> + HasDefId> SInto<S, TraitItem> for rustc_hir::TraitItemRef {
    fn sinto(&self, s: &S) -> TraitItem {
        let tcx: rustc_middle::ty::TyCtxt = s.tcx();
        tcx.hir().trait_item(self.clone().id).sinto(s)
    }
}

use itertools::Itertools;

pub fn inline_macro_invokations<'t, S: BaseState<'t>>(
    ids: &Vec<rustc_hir::ItemId>,
    s: &S,
) -> Vec<Item> {
    let tcx: rustc_middle::ty::TyCtxt = s.tcx();
    let hir = tcx.hir();

    struct SpanEq(Option<(DefId, rustc_span::hygiene::ExpnData)>);
    impl core::cmp::PartialEq for SpanEq {
        fn eq(&self, other: &SpanEq) -> bool {
            let project = |x: &SpanEq| x.0.clone().map(|x| x.1.call_site);
            project(self) == project(other)
        }
    }

    ids.iter()
        .cloned()
        .map(|id| tcx.hir().item(id))
        .group_by(|item| SpanEq(raw_macro_invokation_of_span(item.span, s)))
        .into_iter()
        .map(|(mac, items)| match mac.0 {
            Some((macro_ident, expn_data)) => {
                let invokation =
                    macro_invokation_of_raw_mac_invokation(&macro_ident, &expn_data, s);
                let span = expn_data.call_site.sinto(s);
                vec![Item {
                    def_id: None,
                    owner_id: expn_data.parent_module.unwrap().sinto(s),
                    kind: ItemKind::MacroInvokation(invokation),
                    span,
                    vis_span: rustc_span::DUMMY_SP.sinto(s),
                }]
            }
            _ => items.map(|item| item.sinto(s)).collect(),
        })
        .flatten()
        .collect()
}

impl<'a, 'tcx, S: BaseState<'tcx>> SInto<S, Vec<Item>> for rustc_hir::Mod<'a> {
    fn sinto(&self, s: &S) -> Vec<Item> {
        inline_macro_invokations(&self.item_ids.iter().cloned().collect(), s)
        // .iter()
        // .map(|item_id| item_id.sinto(s))
        // .collect()
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::ForeignItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ForeignItemKind {
    Fn(FnDecl, Vec<Ident>, Generics),
    Static(Ty, Mutability),
    Type,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::ForeignItem<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ForeignItem {
    pub ident: Ident,
    pub kind: ForeignItemKind,
    pub owner_id: OwnerId,
    pub span: Span,
    pub vis_span: Span,
}

impl<'a, S: BaseState<'a> + HasDefId> SInto<S, ForeignItem> for rustc_hir::ForeignItemRef {
    fn sinto(&self, s: &S) -> ForeignItem {
        let tcx: rustc_middle::ty::TyCtxt = s.tcx();
        tcx.hir().foreign_item(self.clone().id).sinto(s)
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::OpaqueTy<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct OpaqueTy {
    pub generics: Generics,
    pub bounds: GenericBounds,
    pub origin: OpaqueTyOrigin,
    pub in_trait: bool,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::LifetimeName, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum LifetimeName {
    Param(GlobalIdent),
    ImplicitObjectLifetimeDefault,
    Error,
    Infer,
    Static,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::Lifetime, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Lifetime {
    pub hir_id: HirId,
    pub ident: Ident,
    pub res: LifetimeName,
}

/*
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::TraitRef<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitRef {
    #[map(vec![])] //TODO!
    pub path: Path,
    pub hir_ref_id: HirId,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::PolyTraitRef<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct PolyTraitRef {
    pub bound_generic_params: Vec<GenericParam>,
    pub trait_ref: TraitRef,
    pub span: Span,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::TraitBoundModifier, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum TraitBoundModifier {
    None,
    Maybe,
    MaybeConst,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::Term<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Term {
    Ty(Ty),
    Const(AnonConst),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::TypeBindingKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum TypeBindingKind {
    Constraint { bounds: Vec<GenericBound> },
    Equality { term: Term },
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::TypeBinding<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TypeBinding {
    pub hir_id: HirId,
    pub ident: Ident,
    pub gen_args: GenericArgs,
    pub kind: TypeBindingKind,
    pub span: Span,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::GenericArgs<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct GenericArgs {
    #[map(vec![])]
    pub args: Vec<GenericArg>,
    #[map(vec![])]
    pub bindings: Vec<TypeBinding>,
    pub parenthesized: bool,
    pub span_ext: Span,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::GenericBound<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum GenericBound {
    Trait(PolyTraitRef, TraitBoundModifier),
    // LangItemTrait(LangItem, Span, HirId, GenericArgs),
    Outlives(Lifetime),
    #[todo]
    Todo(String),
}
 */

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::TraitRef<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitRef {
    pub def_id: DefId,
    pub substs: Vec<GenericArg>,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::TraitPredicate<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
    #[from(constness)]
    #[map(x.clone() == rustc_middle::ty::BoundConstness::ConstIfConst)]
    pub is_const: bool,
    #[map(x.clone() == rustc_middle::ty::ImplPolarity::Positive)]
    #[from(polarity)]
    pub is_positive: bool,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::Clause<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Clause {
    Trait(TraitPredicate),
    #[todo]
    Todo(String),
    // RegionOutlives(RegionOutlivesPredicate<'tcx>),
    // TypeOutlives(TypeOutlivesPredicate<'tcx>),
    // Projection(ProjectionPredicate<'tcx>),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::PredicateKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum PredicateKind {
    Clause(Clause),
    // WellFormed(GenericArg),
    ObjectSafe(DefId),
    // ClosureKind(DefId, SubstsRef, ClosureKind),
    // Subtype(SubtypePredicate),
    // Coerce(CoercePredicate),
    // ConstEvaluatable(Const),
    // ConstEquate(Const, Const),
    // TypeWellFormedFromEnv(Ty),
    Ambiguous,
    #[todo]
    Todo(String),
}

type GenericBounds = Vec<PredicateKind>;

impl<'tcx, S: BaseState<'tcx> + HasDefId> SInto<S, GenericBounds>
    for rustc_hir::GenericBounds<'tcx>
{
    fn sinto(&self, s: &S) -> GenericBounds {
        let tcx = s.tcx();
        let hir_id = tcx.hir().local_def_id_to_hir_id(s.def_id().expect_local());
        // eprintln!("tcx.hir().get(hir_id)={:#?}", tcx.hir().get(hir_id));
        // let generics = tcx.generics_of(s.def_id());
        let predicates = tcx.predicates_of(s.def_id()).predicates;
        predicates
            .iter()
            .map(|(pred, span)| {
                let pred: rustc_middle::ty::Predicate = pred.clone();
                let kind: rustc_middle::ty::Binder<'_, rustc_middle::ty::PredicateKind> =
                    pred.kind();
                let kind: rustc_middle::ty::PredicateKind = kind.no_bound_vars().unwrap();
                kind.sinto(s)
            })
            .collect()
        // eprintln!("generics={:#?}", generics);
        // eprintln!("predicates={:#?}", predicates);
        // match tcx.hir().get(hir_id)
        // let ctx = rustc_hir_analysis::collect::ItemCtxt::new(tcx, s.def_id());
        // let x = tcx.explicit_item_bounds(s.def_id());
        // x.iter().map(|(pred, span)| {
        //     let pred: rustc_middle::ty::Predicate = pred.clone();
        //     let kind: rustc_middle::ty::Binder<'_, rustc_middle::ty::PredicateKind>
        //         = pred.kind();
        //     let kind: rustc_middle::ty::PredicateKind = kind.no_bound_vars().unwrap();
        //     kind.sinto(s)
        // }).collect()
        // let _ = ctx.to_ty(self).sinto(s);
        // let self_param_ty = tcx.types.self_param;
        // let x = ctx.compute_bounds_inner(self_param_ty, []);
        // let tcx: rustc_middle::ty::TyCtxt = s.tcx();
        // tcx.hir().item(self.clone()).sinto(s)
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::OpaqueTyOrigin, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum OpaqueTyOrigin {
    FnReturn(GlobalIdent),
    AsyncFn(GlobalIdent),
    TyAlias,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::MacroDef, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct MacroDef {
    pub body: DelimArgs,
    pub macro_rules: bool,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::Item<'tcx>, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Item {
    #[map({
        let name: String = self.ident.name.to_ident_string();
        let owner_id: DefId = self.owner_id.sinto(state);
        let path = Path::from(owner_id.clone());
        if path.ends_with(&[name]) {Some(owner_id.clone())} else {None}
    })]
    #[not_in_source]
    pub def_id: Option<GlobalIdent>,
    pub owner_id: DefId,
    pub span: Span,
    pub vis_span: Span,
    #[map({
        self.kind.sinto(&State {
            tcx: state.tcx(),
            options: state.options(),
            thir: (),
            def_id: self.owner_id.to_def_id(),
            opt_def_id: Some(self.owner_id.to_def_id()),
            macro_infos: state.macro_infos(),
            local_ident_map: state.local_ident_map(),
        })
    })]
    pub kind: ItemKind,
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, Item> for rustc_hir::ItemId {
    fn sinto(&self, s: &S) -> Item {
        let tcx: rustc_middle::ty::TyCtxt = s.tcx();
        tcx.hir().item(self.clone()).sinto(s)
    }
}

// pub type GenericBounds = Vec<GenericBound>;

// #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub type Ident = (Symbol, Span);
// pub struct Ident {
// pub name: String,
//     pub span: Span,
//     pub id: u32,
// }

impl<'tcx, S: BaseState<'tcx>> SInto<S, Ident> for rustc_span::symbol::Ident {
    fn sinto(&self, s: &S) -> Ident {
        (self.name.sinto(s), self.span.sinto(s))
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasDefId>, from: rustc_hir::WhereBoundPredicate<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct WhereBoundPredicate {
    pub hir_id: HirId,
    pub span: Span,
    pub origin: PredicateOrigin,
    pub bound_generic_params: Vec<GenericParam>,
    pub bounded_ty: Ty,
    pub bounds: GenericBounds,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::PredicateOrigin, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum PredicateOrigin {
    WhereClause,
    GenericParam,
    ImplTrait,
}

sinto_todo!(rustc_hir, InlineAsm<'a>);
sinto_todo!(rustc_hir, UsePath<'tcx>);
sinto_todo!(rustc_target::spec::abi, Abi);
sinto_todo!(rustc_hir, WhereRegionPredicate<'tcx>);
sinto_todo!(rustc_hir, WhereEqPredicate<'tcx>);
sinto_todo!(rustc_hir, OwnerId);
