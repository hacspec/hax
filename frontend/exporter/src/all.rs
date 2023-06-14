use crate::state::*;
use schemars::{schema_for, JsonSchema};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

use crate::{AdtInto, SInto};

pub trait BaseState<'tcx> = HasTcx<'tcx>
    + HasOptions
    + HasMacroInfos
    + HasLocalCtx
    + IsState<'tcx>
    + Clone
    + HasOptDefId
    + HasCachedThirs<'tcx>
    + HasExportedSpans;
// + std::fmt::Debug;

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct DefId {
    pub krate: String,
    pub path: Vec<DefPathItem>,
}

pub type Path = Vec<String>; // x::y::z, TODO
pub type ProjectionPath = Vec<String>; // x::y::z, TODO
                                       // pub type LitFloatType = TODO;

macro_rules! supposely_unreachable {
    (@$verb:tt $label:literal : $($e:expr),*$(,)?) => {
        $verb !(concat!("
Supposely unreachable place in the Rust AST. The label is ", stringify!($label), ".
This ", stringify!($verb), " happend because I thought some node in the Rust AST could not show up under certain condition(s).

Please report that message along with the crate!

Meta-information:
", $(stringify!( - $e: ), " {:#?}", "\n",)*), $($e,)*);
    };
    ($($t:tt)*) => {
        #[cfg(feature = "minimal-ast")] supposely_unreachable!(@eprintln $($t)*);
        #[cfg(not(feature = "minimal-ast"))] supposely_unreachable!(@println $($t)*);
    };
}

impl std::convert::From<DefId> for Path {
    fn from(v: DefId) -> Vec<String> {
        std::iter::once(v.krate)
            .chain(v.path.into_iter().filter_map(|item| match item {
                DefPathItem::TypeNs(s)
                | DefPathItem::ValueNs(s)
                | DefPathItem::MacroNs(s)
                | DefPathItem::LifetimeNs(s) => Some(s),
                _ => None,
            }))
            .collect()
    }
}

impl<'s, S: BaseState<'s>> SInto<S, DefId> for rustc_hir::def_id::DefId {
    fn sinto(&self, s: &S) -> DefId {
        let tcx = s.tcx();
        let def_path = tcx.def_path(self.clone());
        let krate = tcx.crate_name(def_path.krate);
        DefId {
            path: def_path.data.iter().map(|x| x.data.sinto(s)).collect(),
            krate: format!("{}", krate),
        }
    }
}

pub type GlobalIdent = DefId;
impl<'tcx, S: BaseState<'tcx>> SInto<S, GlobalIdent> for rustc_hir::def_id::LocalDefId {
    fn sinto(&self, st: &S) -> DefId {
        self.to_def_id().sinto(st)
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'a, S>, from: rustc_middle::thir::LogicalOp, state: S as s)]
pub enum LogicalOp {
    And,
    Or,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'a, S: BaseState<'a>>, from: rustc_hir::definitions::DefPathData, state: S as s)]
pub enum DefPathItem {
    CrateRoot,
    Impl,
    ForeignMod,
    Use,
    GlobalAsm,
    TypeNs(Symbol),
    ValueNs(Symbol),
    MacroNs(Symbol),
    LifetimeNs(Symbol),
    ClosureExpr,
    Ctor,
    AnonConst,
    ImplTrait,
    ImplTraitAssocTy,
}

pub type Symbol = String;
impl<'t, S> SInto<S, Symbol> for rustc_span::symbol::Symbol {
    fn sinto(&self, s: &S) -> Symbol {
        self.to_ident_string()
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'slt, S: BaseState<'slt> + HasThir<'slt>>, from: rustc_middle::thir::LintLevel, state: S as gstate)]
pub enum LintLevel {
    Inherited,
    Explicit(HirId),
}

pub type Mutability = bool;
impl<S> SInto<S, Mutability> for rustc_hir::Mutability {
    fn sinto(&self, s: &S) -> Mutability {
        match self {
            rustc_hir::Mutability::Mut => true,
            _ => false,
        }
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_ast::ast::AttrStyle, state: S as gstate)]
pub enum AttrStyle {
    Outer,
    Inner,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'slt, S: BaseState<'slt>>, from: rustc_ast::ast::Attribute, state: S as gstate)]
pub struct Attribute {
    pub kind: AttrKind,
    #[map(x.as_usize())]
    pub id: usize,
    pub style: AttrStyle,
    pub span: Span,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Decorated<T> {
    pub ty: Ty,
    pub span: Span,
    pub contents: Box<T>,
    pub hir_id: Option<(usize, usize)>,
    pub attributes: Vec<Attribute>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'slt, S: BaseState<'slt> + HasThir<'slt>>, from: rustc_middle::mir::UnOp, state: S as gstate)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'slt, S: BaseState<'slt> + HasThir<'slt>>, from: rustc_middle::mir::BinOp, state: S as gstate)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Offset,
}

pub type Pat = Decorated<PatKind>;
pub type Expr = Decorated<ExprKind>;

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::middle::region::ScopeData, state: S as gstate)]
pub enum ScopeData {
    Node,
    CallSite,
    Arguments,
    Destruction,
    IfThen,
    Remainder(FirstStatementIndex),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::middle::region::Scope, state: S as gstate)]
pub struct Scope {
    pub id: ItemLocalId,
    pub data: ScopeData,
}

impl<'tcx, S: BaseState<'tcx> + HasThir<'tcx>> SInto<S, ConstantKind>
    for rustc_middle::mir::ConstantKind<'tcx>
{
    fn sinto(&self, s: &S) -> ConstantKind {
        use rustc_middle::mir::ConstantKind as RustConstantKind;
        match self.eval(s.tcx(), get_param_env(s)) {
            RustConstantKind::Val(const_value, ty) => {
                use rustc_middle::mir::interpret::ConstValue;
                match const_value {
                    ConstValue::Scalar(scalar) => {
                        ConstantKind::Lit(scalar_int_to_literal(s, scalar.assert_int(), ty.clone()))
                    }
                    _ => ConstantKind::Todo(format!("{:#?}", self)),
                }
            }
            RustConstantKind::Ty(c) => match c.kind().try_to_scalar_int() {
                Some(si) => ConstantKind::Lit(scalar_int_to_literal(s, si, c.ty())),
                _ => ConstantKind::Ty(c.sinto(s)),
            },
            _ => ConstantKind::Todo(format!("{:#?}", self)),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ConstantKind {
    Ty(Const),
    // Unevaluated(Unevaluated<'tcx, Option<Promoted>>, Ty),
    Lit(LitKind),

    // Val(ConstValue, Ty),
    Todo(String),
}

// #[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
// #[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::mir::interpret::ConstValue<'tcx>, state: S as gstate)]
// pub enum ConstValue {
//     #[from(Scalar)]
//     Literal(
//         #[map({
//             use rustc_middle::{mir::interpret::Scalar, ty::consts::int::ScalarInt};
//             match x {
//                 FROM_TYPE::Int ({data, size}) => todo!(),
//                 Scalar::Ptr(..) => panic!("Ptr")
//             }
//         })]
//         LitKind,
//     ),
//     // Scalar(Scalar),
//     ZeroSized,
//     Slice {
//         data: ConstAllocation,
//         start: usize,
//         end: usize,
//     },
//     // ByRef {
//     //     alloc: ConstAllocation,
//     //     offset: Size,
//     // },
//     #[todo]
//     Todo(String),
// }

impl<S> SInto<S, u64> for rustc_middle::mir::interpret::AllocId {
    fn sinto(&self, s: &S) -> u64 {
        self.0.get()
    }
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, Box<Ty>> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Box<Ty> {
        Box::new(self.sinto(s))
    }
}

// impl<'s, 'a, S: BaseState<'a>>
impl<'tcx, S: BaseState<'tcx>> SInto<S, Ty> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Ty {
        self.kind().sinto(s)
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::hir_id::HirId, state: S as gstate)]
pub struct HirId {
    owner: DefId,
    local_id: usize,
    // attrs: String
}
// TODO: If not working: See original

impl<'tcx, S: BaseState<'tcx>> SInto<S, DefId> for rustc_hir::hir_id::OwnerId {
    fn sinto(&self, s: &S) -> DefId {
        self.to_def_id().sinto(s)
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_ast::ast::LitFloatType, state: S as gstate)]
pub enum LitFloatType {
    Suffixed(FloatTy),
    Unsuffixed,
}
#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S>, from: rustc_hir::Movability, state: S as gstate)]
pub enum Movability {
    Static,
    Movable,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::infer::canonical::CanonicalTyVarKind, state: S as gstate)]
pub enum CanonicalTyVarKind {
    General(UniverseIndex),
    Int,
    Float,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::ParamTy, state: S as gstate)]
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::ty::ParamConst, state: S as gstate)]
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::ty::DynKind, state: S as gstate)]
pub enum DynKind {
    Dyn,
    DynStar,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::BoundTyKind, state: S as gstate)]
pub enum BoundTyKind {
    Anon,
    Param(DefId, Symbol),
}

pub type Const = Box<Expr>;

impl<'tcx, S: BaseState<'tcx>> SInto<S, Const> for rustc_middle::ty::Const<'tcx> {
    fn sinto(&self, s: &S) -> Const {
        let x = self.eval(s.tcx(), get_param_env(s));
        use rustc_middle::query::Key;
        Box::new(const_to_expr(s, x.clone(), x.ty(), x.default_span(s.tcx())))
    }
}

use crate::{sinto_as_usize, sinto_todo};
sinto_todo!(rustc_middle::mir::interpret, Scalar);
sinto_todo!(rustc_middle::ty, ScalarInt);

sinto_todo!(rustc_middle::ty, ExistentialPredicate<'a>);
sinto_todo!(rustc_middle::ty, Region<'s>);
sinto_todo!(rustc_middle::ty, PolyFnSig<'s>);
sinto_todo!(rustc_middle::ty, AdtFlags);
sinto_todo!(rustc_middle::mir::interpret, ConstAllocation<'a>);

sinto_as_usize!(rustc_middle::ty, DebruijnIndex);
sinto_as_usize!(rustc_middle::ty, UniverseIndex);
sinto_as_usize!(rustc_middle::ty, BoundVar);
sinto_as_usize!(rustc_middle::middle::region, FirstStatementIndex);

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::BoundTy, state: S as gstate)]
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::BoundRegionKind, state: S as gstate)]
pub enum BoundRegionKind {
    BrAnon(Option<Span>),
    BrNamed(DefId, Symbol),
    BrEnv,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::BoundRegion, state: S as gstate)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

pub type PlaceholderRegion = Placeholder<BoundRegion>;
pub type PlaceholderConst = Placeholder<BoundVar>;
pub type PlaceholderType = Placeholder<BoundTy>;

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Placeholder<T> {
    pub universe: UniverseIndex,
    pub bound: T,
}

impl<'tcx, S: BaseState<'tcx>, T: SInto<S, U>, U> SInto<S, Placeholder<U>>
    for rustc_middle::ty::Placeholder<T>
{
    fn sinto(&self, s: &S) -> Placeholder<U> {
        Placeholder {
            universe: self.universe.sinto(s),
            bound: self.bound.sinto(s),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Canonical<T> {
    pub max_universe: UniverseIndex,
    pub variables: Vec<CanonicalVarInfo>,
    pub value: T,
}
pub type CanonicalUserType = Canonical<UserType>;

impl<'tcx, S: BaseState<'tcx> + HasThir<'tcx>, T: SInto<S, U>, U> SInto<S, Canonical<U>>
    for rustc_middle::infer::canonical::Canonical<'tcx, T>
{
    fn sinto(&self, s: &S) -> Canonical<U> {
        Canonical {
            max_universe: self.max_universe.sinto(s),
            variables: self.variables.iter().map(|v| v.kind.sinto(s)).collect(),
            value: self.value.sinto(s),
        }
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::infer::canonical::CanonicalVarKind<'tcx>, state: S as gstate)]
pub enum CanonicalVarInfo {
    Ty(CanonicalTyVarKind),
    PlaceholderTy(PlaceholderType),
    Region(UniverseIndex),
    PlaceholderRegion(PlaceholderRegion),
    Const(UniverseIndex, Ty),
    PlaceholderConst(PlaceholderConst, Ty),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::subst::UserSelfTy<'tcx>, state: S as gstate)]
pub struct UserSelfTy {
    pub impl_def_id: DefId,
    pub self_ty: Ty,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::subst::UserSubsts<'tcx>, state: S as gstate)]
pub struct UserSubsts {
    pub substs: Vec<GenericArg>,
    pub user_self_ty: Option<UserSelfTy>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::UserType<'tcx>, state: S as gstate)]
pub enum UserType {
    Ty(Ty),
    TypeOf(DefId, UserSubsts),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_hir::def::CtorKind, state: S as gstate)]
pub enum CtorKind {
    Fn,
    Const,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::VariantDiscr, state: S as gstate)]
pub enum VariantDiscr {
    Explicit(DefId),
    Relative(u32),
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Visibility<Id = rustc_span::def_id::LocalDefId> {
    Public,
    Restricted(Id),
}
impl<S, T: SInto<S, U>, U> SInto<S, Visibility<U>> for rustc_middle::ty::Visibility<T> {
    fn sinto(&self, s: &S) -> Visibility<U> {
        use rustc_middle::ty::Visibility as T;
        match self {
            T::Public => Visibility::Public,
            T::Restricted(id) => Visibility::Restricted(id.sinto(s)),
        }
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::FieldDef, state: S as state)]
pub struct FieldDef {
    pub did: DefId,
    pub name: Symbol,
    pub vis: Visibility<DefId>,
}

// impl<I: rustc_index::vec::Idx, S, D: Clone, T: SInto<S, D>> SInto<S, Vec<D>>
//     for rustc_index::vec::IndexVec<I, T>
// {
//     fn sinto(&self, s: &S) -> Vec<D> {
//         self.into_iter().map(|x| x.sinto(s)).collect()
//     }
// }

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::VariantDef, state: S as state)]
pub struct VariantDef {
    pub def_id: DefId,
    #[map(todo!())]
    pub ctor: Option<(CtorKind, DefId)>,
    pub name: Symbol,
    pub discr: VariantDiscr,
    #[map(fields.raw.sinto(state))]
    pub fields: Vec<FieldDef>,
}

sinto_as_usize!(rustc_hir::hir_id, ItemLocalId);
sinto_as_usize!(rustc_target::abi, VariantIdx);

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::subst::GenericArgKind<'tcx>, state: S as gstate)]
pub enum GenericArg {
    Lifetime(Region),
    Type(Ty),
    Const(Const),
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, Vec<GenericArg>>
    for rustc_middle::ty::subst::SubstsRef<'tcx>
{
    fn sinto(&self, s: &S) -> Vec<GenericArg> {
        self.iter().map(|v| v.unpack().sinto(s)).collect()
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_ast::ast::LitIntType, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum LitIntType {
    Signed(IntTy),
    Unsigned(UintTy),
    Unsuffixed,
}

pub type AdtDef = DefId;
impl<'a, 's, S: BaseState<'s>> SInto<S, AdtDef> for rustc_middle::ty::AdtDef<'a> {
    fn sinto(&self, s: &S) -> AdtDef {
        self.did().sinto(s)
    }
}

// #[derive(AdtInto)]
// #[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::AdtExpr<'tcx>, state: S as gstate)]
// #[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
// pub struct AdtExpr {
//     pub adt_def: DefId,
//     pub variant_index: VariantIdx,
//     pub substs: Vec<GenericArg>,
//     pub user_ty: Option<CanonicalUserType>,
//     pub fields: Vec<FieldExpr>,
//     pub base: Option<FruInfo>,
// }

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::FruInfo<'tcx>, state: S as gstate)]
// Field renaming u.. ?
pub struct FruInfo {
    pub base: Expr,
    pub field_types: Vec<Ty>,
}

// #[derive(AdtInto)]
// #[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::FieldExpr, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct FieldExpr {
    pub field: DefId,
    pub value: Expr,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
// #[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::FieldPat<'tcx>, state: S as gstate)]
pub struct FieldPat {
    pub field: DefId,
    pub pattern: Pat,
}

impl<'tcx, S: ExprState<'tcx>> SInto<S, AdtExpr> for rustc_middle::thir::AdtExpr<'tcx> {
    fn sinto(&self, s: &S) -> AdtExpr {
        let variants = self.adt_def.variants();
        let variant: &rustc_middle::ty::VariantDef = &variants[self.variant_index];
        AdtExpr {
            info: get_variant_information(&self.adt_def, &variant.def_id, s),
            fields: self
                .fields
                .iter()
                .map(|f| FieldExpr {
                    field: variant.fields[f.name].did.sinto(s),
                    value: f.expr.sinto(s),
                })
                .collect(),
            base: self.base.sinto(s),
            user_ty: self.user_ty.sinto(s),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
pub struct Loc {
    line: usize,
    col: usize,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::DesugaringKind, state: S as gstate)]
pub enum DesugaringKind {
    CondTemporary,
    QuestionMark,
    TryBlock,
    YeetExpr,
    OpaqueTy,
    Async,
    Await,
    ForLoop,
    WhileLoop,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::AstPass, state: S as gstate)]
pub enum AstPass {
    StdImports,
    TestHarness,
    ProcMacroHarness,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::MacroKind, state: S as gstate)]
pub enum MacroKind {
    Bang,
    Attr,
    Derive,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_span::hygiene::ExpnKind, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ExpnKind {
    Root,
    Macro(MacroKind, Symbol),
    AstPass(AstPass),
    Desugaring(DesugaringKind),
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_span::edition::Edition, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Edition {
    Edition2015,
    Edition2018,
    Edition2021,
    Edition2024,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_span::hygiene::ExpnData, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ExpnData {
    pub kind: ExpnKind,
    // pub parent: Box<ExpnData>,
    pub call_site: Span,
    pub def_site: Span,
    #[map(x.as_ref().map(|x| x.clone().iter().map(|x|x.sinto(state)).collect()))]
    pub allow_internal_unstable: Option<Vec<Symbol>>,
    pub edition: Edition,
    pub macro_def_id: Option<DefId>,
    pub parent_module: Option<DefId>,
    pub allow_internal_unsafe: bool,
    pub local_inner_macros: bool,
    pub collapse_debuginfo: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
pub struct Span {
    lo: Loc,
    hi: Loc,
    filename: FileName,
    // expn_backtrace: Vec<ExpnData>,
}

#[derive(Debug)]
pub enum ReadSpanErr {
    NotRealFileName(String),
    WhileReading(std::io::Error),
    NotEnoughLines { span: Span },
    Todo,
}
impl std::convert::From<std::io::Error> for ReadSpanErr {
    fn from(value: std::io::Error) -> Self {
        ReadSpanErr::WhileReading(value)
    }
}

fn read_span_from_file(span: &Span) -> Result<String, ReadSpanErr> {
    use ReadSpanErr::*;
    let realpath = (match span.filename.clone() {
        FileName::Real(RealFileName::LocalPath(path)) => Ok(path),
        _ => Err(NotRealFileName(format!("{:#?}", span.filename))),
    })?;
    use std::fs::File;
    use std::io::{self, prelude::*, BufReader};
    let file = File::open(realpath)?;
    let reader = BufReader::new(file);
    let lines = reader
        .lines()
        .skip(span.lo.line - 1)
        .take(span.hi.line - span.lo.line + 1)
        .collect::<Result<Vec<_>, _>>()?;

    match lines.as_slice() {
        [] => Err(NotEnoughLines { span: span.clone() }),
        [line] => Ok(line
            .chars()
            .enumerate()
            .filter(|(i, _)| *i >= span.lo.col && *i < span.hi.col)
            .map(|(_, c)| c)
            .collect()),
        [first, middle @ .., last] => {
            let first = first.chars().skip(span.lo.col).collect();
            let last = last.chars().take(span.hi.col).collect();
            Ok(std::iter::once(first)
                .chain(middle.into_iter().cloned())
                .chain(std::iter::once(last))
                .collect::<Vec<String>>()
                .join("\n"))
        }
    }
}

impl Into<Loc> for rustc_span::Loc {
    fn into(self) -> Loc {
        Loc {
            line: self.line,
            col: self.col_display,
        }
    }
}

pub fn translate_span(span: rustc_span::Span, sess: &rustc_session::Session) -> Span {
    let smap: &rustc_span::source_map::SourceMap = sess.parse_sess.source_map();
    let span_data = span.data();
    let filename = smap.span_to_filename(span);

    let lo = smap.lookup_char_pos(span.lo());
    let hi = smap.lookup_char_pos(span.hi());

    Span {
        lo: lo.into(),
        hi: hi.into(),
        filename: filename.sinto(&()),
    }
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, Span> for rustc_span::Span {
    fn sinto(&self, s: &S) -> Span {
        let set: crate::state::types::ExportedSpans = s.exported_spans();
        set.borrow_mut().insert(self.clone());
        translate_span(self.clone(), s.tcx().sess)
    }
}

// sinto_as_usize!(rustc_middle::mir, Field);

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct LocalIdent {
    pub name: String,
    pub id: HirId,
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, LocalIdent> for rustc_middle::thir::LocalVarId {
    fn sinto(&self, s: &S) -> LocalIdent {
        LocalIdent {
            name: s
                .local_ctx()
                .borrow()
                .vars
                .get(self)
                .clone()
                .unwrap()
                .to_string(),
            id: self.clone().0.sinto(s),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}
impl<'s, S: BaseState<'s>, T: SInto<S, U>, U> SInto<S, Spanned<U>>
    for rustc_span::source_map::Spanned<T>
{
    fn sinto<'a>(&self, s: &S) -> Spanned<U> {
        Spanned {
            node: self.node.sinto(s),
            span: self.span.sinto(s),
        }
    }
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, String> for PathBuf {
    fn sinto(&self, s: &S) -> String {
        self.as_path().display().to_string()
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
#[args(<S>, from: rustc_span::RealFileName, state: S as gstate)]
pub enum RealFileName {
    LocalPath(#[map(x.to_str().unwrap().into())] String),
    #[map(RealFileName::Remapped {
            local_path: local_path.as_ref().map(|path| path.to_str().unwrap().into()),
            virtual_name: virtual_name.to_str().unwrap().into()
        })]
    Remapped {
        local_path: Option<String>,
        virtual_name: String,
    },
}

impl<S> SInto<S, u64> for rustc_data_structures::stable_hasher::Hash64 {
    fn sinto(&self, s: &S) -> u64 {
        self.as_u64()
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_span::FileName, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
pub enum FileName {
    Real(RealFileName),
    QuoteExpansion(u64),
    Anon(u64),
    MacroExpansion(u64),
    ProcMacroSourceCode(u64),
    CfgSpec(u64),
    CliCrateAttr(u64),
    Custom(String),
    // #[map(FileName::DocTest(x.0.to_str().unwrap().into()))]
    #[custom_arm(FROM_TYPE::DocTest(x, _) => TO_TYPE::DocTest(x.to_str().unwrap().into()),)]
    DocTest(String),
    InlineAsm(u64),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S>, from: rustc_middle::ty::InferTy, state: S as gstate)]
pub enum InferTy {
    #[custom_arm(FROM_TYPE::TyVar(..) => TO_TYPE::TyVar,)]
    TyVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::IntVar(..) => TO_TYPE::IntVar,)]
    IntVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::FloatVar(..) => TO_TYPE::FloatVar,)]
    FloatVar, /*TODO?*/
    FreshTy(u32),
    FreshIntTy(u32),
    FreshFloatTy(u32),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S>, from: rustc_middle::thir::BlockSafety, state: S as gstate)]
pub enum BlockSafety {
    Safe,
    BuiltinUnsafe,
    #[custom_arm(FROM_TYPE::ExplicitUnsafe{..} => BlockSafety::ExplicitUnsafe,)]
    ExplicitUnsafe,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Block, state: S as gstate)]
pub struct Block {
    pub targeted_by_break: bool,
    pub region_scope: Scope,
    pub opt_destruction_scope: Option<Scope>,
    pub span: Span,
    pub stmts: Vec<Stmt>,
    pub expr: Option<Expr>,
    pub safety_mode: BlockSafety,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct AliasTy {
    pub substs: Vec<GenericArg>,
    pub trait_def_id: DefId,
}

fn get_param_env<'tcx, S: BaseState<'tcx>>(s: &S) -> rustc_middle::ty::ParamEnv<'tcx> {
    match s.opt_def_id() {
        Some(id) => s.tcx().param_env(id),
        None => rustc_middle::ty::ParamEnv::empty(),
    }
}

fn _resolve_trait<'tcx, S: BaseState<'tcx>>(trait_ref: rustc_middle::ty::TraitRef<'tcx>, s: &S) {
    let tcx = s.tcx();
    let param_env = get_param_env(s);
    use rustc_middle::ty::Binder;
    let binder: Binder<'tcx, _> = Binder::dummy(trait_ref);
    // let x: Result<&rustc_middle::traits::ImplSource<'tcx, ()>, _> =
    //     tcx.codegen_select_candidate((param_env, binder));
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_infer::traits;
    use rustc_middle::ty::{ParamEnv, ParamEnvAnd};
    use rustc_trait_selection::infer::InferCtxtBuilderExt;
    use rustc_trait_selection::traits::SelectionContext;
    // let id = s.opt_def_id().unwrap();
    let inter_ctxt = tcx.infer_ctxt().ignoring_regions().build();
    let mut selection_ctxt = SelectionContext::new(&inter_ctxt);
    use std::collections::VecDeque;
    let mut queue = VecDeque::new();
    let obligation = traits::Obligation::new(
        tcx,
        traits::ObligationCause::dummy(),
        param_env,
        rustc_middle::ty::Binder::dummy(trait_ref),
    );
    use rustc_middle::traits::ImplSource;
    queue.push_back(obligation);
    loop {
        match queue.pop_front() {
            Some(obligation) => {
                let impl_source = selection_ctxt.select(&obligation).unwrap().unwrap();
                println!("impl_source={:#?}", impl_source);
                let nested = impl_source.clone().nested_obligations();
                for subobligation in nested {
                    let bound_predicate = subobligation.predicate.kind();
                    match bound_predicate.skip_binder() {
                        rustc_middle::ty::PredicateKind::Clause(
                            rustc_middle::ty::Clause::Trait(trait_pred),
                        ) => {
                            let trait_pred = bound_predicate.rebind(trait_pred);
                            let subobligation = subobligation.with(tcx, trait_pred);
                            queue.push_back(subobligation);
                        }
                        _ => (),
                    }
                }
            }
            None => break,
        }
    }
    // let impl_source = selection_ctxt.select(&obligation).unwrap().unwrap();
    // let nested = impl_source.clone().nested_obligations();
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, AliasTy> for rustc_middle::ty::AliasTy<'tcx> {
    fn sinto(&self, s: &S) -> AliasTy {
        let tcx = s.tcx();
        let trait_ref = self.trait_ref(tcx);
        // resolve_trait(trait_ref, s);
        AliasTy {
            substs: self.substs.sinto(s),
            trait_def_id: self.trait_def_id(tcx).sinto(s),
        }
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::thir::BindingMode, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum BindingMode {
    ByValue,
    ByRef(BorrowKind),
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Stmt<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Stmt {
    pub kind: StmtKind,
    pub opt_destruction_scope: Option<Scope>,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::MacDelimiter, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum MacDelimiter {
    Parenthesis,
    Bracket,
    Brace,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::Delimiter, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
    Invisible,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::tokenstream::TokenTree, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum TokenTree {
    Token(Token, Spacing),
    Delimited(DelimSpan, Delimiter, TokenStream),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::tokenstream::Spacing, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Spacing {
    Alone,
    Joint,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::BinOpToken, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum BinOpToken {
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    And,
    Or,
    Shl,
    Shr,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::token::TokenKind, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum TokenKind {
    Eq,
    Lt,
    Le,
    EqEq,
    Ne,
    Ge,
    Gt,
    AndAnd,
    OrOr,
    Not,
    Tilde,
    BinOp(BinOpToken),
    BinOpEq(BinOpToken),
    At,
    Dot,
    DotDot,
    DotDotDot,
    DotDotEq,
    Comma,
    Semi,
    Colon,
    ModSep,
    RArrow,
    LArrow,
    FatArrow,
    Pound,
    Dollar,
    Question,
    SingleQuote,
    OpenDelim(Delimiter),
    CloseDelim(Delimiter),
    // Literal(l: Lit),
    Ident(Symbol, bool),
    Lifetime(Symbol),
    // Interpolated(n: Nonterminal),
    // DocComment(k: CommentKind, ats: AttrStyle, s: Symbol),
    Eof,
    #[todo]
    Todo(String),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::token::Token, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::DelimArgs, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct DelimArgs {
    pub dspan: DelimSpan,
    pub delim: MacDelimiter,
    pub tokens: TokenStream,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::MacCall, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct MacCall {
    #[map(x.segments.iter().map(|rustc_ast::ast::PathSegment{ident, ..}| ident.as_str().into()).collect())]
    pub path: Path,
    pub args: DelimArgs,
}

pub type TokenStream = String;
impl<'t, S> SInto<S, TokenStream> for rustc_ast::tokenstream::TokenStream {
    fn sinto(&self, s: &S) -> String {
        rustc_ast_pretty::pprust::tts_to_string(self)
    }
}

sinto_todo!(rustc_ast::tokenstream, DelimSpan);

impl<'tcx, S: ExprState<'tcx>> SInto<S, Block> for rustc_middle::thir::BlockId {
    fn sinto(&self, s: &S) -> Block {
        s.thir().blocks[*self].sinto(s)
    }
}

impl<'tcx, S: ExprState<'tcx>> SInto<S, Stmt> for rustc_middle::thir::StmtId {
    fn sinto(&self, s: &S) -> Stmt {
        s.thir().stmts[*self].sinto(s)
    }
}

pub fn argument_span_of_mac_call(mac_call: &rustc_ast::ast::MacCall) -> rustc_span::Span {
    (*mac_call.args).dspan.entire()
}

pub fn raw_macro_invocation_of_span<'t, S: BaseState<'t>>(
    span: rustc_span::Span,
    state: &S,
) -> Option<(DefId, rustc_span::hygiene::ExpnData)> {
    let box opts: Box<hax_frontend_exporter_options::Options> = state.options();
    let box macro_calls: crate::state::types::MacroCalls = state.macro_infos();

    let sess = state.tcx().sess;

    span.macro_backtrace().find_map(|expn_data| {
        let expn_data_ret = expn_data.clone();
        let call_site = translate_span(expn_data.call_site, sess);
        match (expn_data.kind, expn_data.macro_def_id) {
            (rustc_span::hygiene::ExpnKind::Macro(_, _), Some(mac_def_id))
                if macro_calls.keys().any(|span| span.clone() == call_site) =>
            {
                let macro_ident = mac_def_id.sinto(state);
                let path = Path::from(macro_ident.clone());
                if opts
                    .inline_macro_calls
                    .iter()
                    .any(|pattern| pattern.matches(&path))
                {
                    Some((macro_ident, expn_data_ret))
                } else {
                    None
                }
            }
            _ => None,
        }
    })
}

pub fn macro_invocation_of_raw_mac_invocation<'t, S: BaseState<'t>>(
    macro_ident: &DefId,
    expn_data: &rustc_span::hygiene::ExpnData,
    state: &S,
) -> MacroInvokation {
    let macro_infos = state.macro_infos();
    let mac_call_span = macro_infos
        .get(&translate_span(expn_data.call_site, state.tcx().sess))
        .unwrap_or_else(|| panic!("{:#?}", expn_data.call_site));
    MacroInvokation {
        macro_ident: macro_ident.clone(),
        argument: read_span_from_file(mac_call_span).unwrap(),
        span: expn_data.call_site.sinto(state),
    }
}

pub fn macro_invocation_of_span<'t, S: BaseState<'t>>(
    span: rustc_span::Span,
    state: &S,
) -> Option<MacroInvokation> {
    let (macro_ident, expn_data) = raw_macro_invocation_of_span(span, state)?;
    Some(macro_invocation_of_raw_mac_invocation(
        &macro_ident,
        &expn_data,
        state,
    ))
}

// fn expr_from_id<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>(
//     id: rustc_middle::thir::ExprId,
//     state: &S,
// ) -> rustc_middle::thir::ExprKind<'tcx> {
//     let thir: rustc_middle::thir::Thir = state.get();
//     thir.exprs[id].kind.clone()
// }

pub trait ExprState<'tcx> = BaseState<'tcx> + HasThir<'tcx> + HasOwnerId;

fn attribute_from_scope<'tcx, S: ExprState<'tcx>>(
    s: &S,
    scope: &rustc_middle::middle::region::Scope,
) -> (Option<rustc_hir::hir_id::HirId>, Vec<Attribute>) {
    let owner = s.owner_id();
    let tcx = s.tcx();
    let scope_tree = tcx.region_scope_tree(owner.to_def_id());
    let hir_id = scope.hir_id(scope_tree);
    let tcx = s.tcx();
    let map = tcx.hir();
    let attributes = hir_id
        .map(|hir_id| map.attrs(hir_id).sinto(s))
        .unwrap_or(vec![]);
    (hir_id, attributes)
}

impl<'tcx, S: ExprState<'tcx>> SInto<S, Expr> for rustc_middle::thir::Expr<'tcx> {
    fn sinto(&self, s: &S) -> Expr {
        let (hir_id, attributes) = match &self.kind {
            rustc_middle::thir::ExprKind::Scope {
                region_scope: scope,
                ..
            } => attribute_from_scope(s, scope),
            _ => (None, vec![]),
        };
        let hir_id = hir_id.map(|hir_id| hir_id.index());
        let unrolled = self.unroll_scope(s);
        let rustc_middle::thir::Expr { span, kind, ty, .. } = unrolled;
        let contents = match macro_invocation_of_span(span, s).map(ExprKind::MacroInvokation) {
            Some(contents) => contents,
            None => match kind {
                rustc_middle::thir::ExprKind::ZstLiteral { .. } => match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(def, substs) => {
                        let tcx = s.tcx();
                        let sig = &tcx.fn_sig(*def).subst(tcx, substs);
                        let ret: rustc_middle::ty::Ty = tcx.erase_late_bound_regions(sig.output());
                        let inputs = sig.inputs();
                        let indexes = inputs.skip_binder().iter().enumerate().map(|(i, _)| i);
                        let params = indexes.map(|i| inputs.map_bound(|tys| tys[i]));
                        let params: Vec<rustc_middle::ty::Ty> =
                            params.map(|i| tcx.erase_late_bound_regions(i)).collect();
                        return Expr {
                            contents: Box::new(ExprKind::GlobalName { id: def.sinto(s) }),
                            span: self.span.sinto(s),
                            ty: ty.sinto(s),
                            hir_id,
                            attributes,
                        };
                    }
                    _ => {
                        supposely_unreachable!("ZstLiteral ty≠FnDef(...)": kind, span, ty);
                        kind.sinto(s)
                    }
                },
                rustc_middle::thir::ExprKind::Field {
                    lhs,
                    variant_index,
                    name,
                } => {
                    let lhs_ty = s.thir().exprs[lhs].ty.kind();
                    let idx = variant_index.index();
                    if idx != 0 {
                        supposely_unreachable!(
                            "ExprKindFieldIdxNonZero": kind,
                            span,
                            ty,
                            ty.kind()
                        );
                    };
                    match lhs_ty {
                        rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
                            let variant = adt_def.variant(variant_index);
                            ExprKind::Field {
                                field: variant.fields[name].did.sinto(s),
                                lhs: lhs.sinto(s),
                            }
                        }
                        rustc_middle::ty::TyKind::Tuple(..) => ExprKind::TupleField {
                            field: name.index(),
                            lhs: lhs.sinto(s),
                        },
                        _ => {
                            supposely_unreachable!(
                                "ExprKindFieldBadTy": kind,
                                span,
                                ty.kind(),
                                lhs_ty
                            );
                            panic!()
                        }
                    }
                }
                _ => kind.sinto(s),
            },
        };
        Decorated {
            ty: ty.sinto(s),
            span: span.sinto(s),
            contents: Box::new(contents),
            hir_id,
            attributes,
        }
    }
}

impl<'tcx, S: ExprState<'tcx>> SInto<S, Expr> for rustc_middle::thir::ExprId {
    fn sinto(&self, s: &S) -> Expr {
        s.thir().exprs[*self].sinto(s)
    }
}

impl<'tcx, S: ExprState<'tcx>> SInto<S, Pat> for rustc_middle::thir::Pat<'tcx> {
    fn sinto(&self, s: &S) -> Pat {
        let rustc_middle::thir::Pat { span, kind, ty } = self;
        let contents = match kind {
            rustc_middle::thir::PatKind::Leaf { subpatterns } => match ty.kind() {
                rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
                    (rustc_middle::thir::PatKind::Variant {
                        adt_def: adt_def.clone(),
                        substs,
                        variant_index: rustc_target::abi::VariantIdx::from_usize(0),
                        subpatterns: subpatterns.clone(),
                    })
                    .sinto(s)
                }
                rustc_middle::ty::TyKind::Tuple(types) => PatKind::Tuple {
                    subpatterns: subpatterns
                        .iter()
                        .map(|pat| pat.pattern.clone())
                        .collect::<Vec<_>>()
                        .sinto(s),
                },
                _ => {
                    supposely_unreachable!(
                        "PatLeafNonAdtTy":
                        ty.kind(),
                        kind,
                        span.sinto(s)
                    );
                    panic!()
                }
            },
            _ => kind.sinto(s),
        };
        Decorated {
            ty: ty.sinto(s),
            span: span.sinto(s),
            contents: Box::new(contents),
            hir_id: None,
            attributes: vec![],
        }
    }
}

impl<'tcx, S: ExprState<'tcx>> SInto<S, Arm> for rustc_middle::thir::ArmId {
    fn sinto(&self, s: &S) -> Arm {
        s.thir().arms[*self].sinto(s)
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::IntTy, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::FloatTy, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum FloatTy {
    F32,
    F64,
}

impl<'tcx, S> SInto<S, FloatTy> for rustc_ast::ast::FloatTy {
    fn sinto(&self, s: &S) -> FloatTy {
        use rustc_ast::ast::FloatTy as T;
        match self {
            T::F32 => FloatTy::F32,
            T::F64 => FloatTy::F64,
        }
    }
}

impl<'tcx, S> SInto<S, IntTy> for rustc_ast::ast::IntTy {
    fn sinto(&self, s: &S) -> IntTy {
        use rustc_ast::ast::IntTy as T;
        match self {
            T::Isize => IntTy::Isize,
            T::I8 => IntTy::I8,
            T::I16 => IntTy::I16,
            T::I32 => IntTy::I32,
            T::I64 => IntTy::I64,
            T::I128 => IntTy::I128,
        }
    }
}
impl<'tcx, S> SInto<S, UintTy> for rustc_ast::ast::UintTy {
    fn sinto(&self, s: &S) -> UintTy {
        use rustc_ast::ast::UintTy as T;
        match self {
            T::Usize => UintTy::Usize,
            T::U8 => UintTy::U8,
            T::U16 => UintTy::U16,
            T::U32 => UintTy::U32,
            T::U64 => UintTy::U64,
            T::U128 => UintTy::U128,
        }
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::UintTy, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::TypeAndMut<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TypeAndMut {
    pub ty: Box<Ty>,
    pub mutbl: Mutability,
}

pub type Binder<T> = Option<T>;

impl<
        's,
        S,
        U,
        T: SInto<S, U> + rustc_middle::ty::visit::TypeVisitable<rustc_middle::ty::TyCtxt<'s>>,
    > SInto<S, Binder<U>> for rustc_middle::ty::Binder<'s, T>
{
    fn sinto(&self, s: &S) -> Binder<U> {
        self.clone().no_bound_vars().map(|x| x.sinto(s))
    }
}

impl<S, U, T: SInto<S, U>> SInto<S, Vec<U>> for rustc_middle::ty::List<T> {
    fn sinto(&self, s: &S) -> Vec<U> {
        self.iter().map(|x| x.sinto(s)).collect()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ArrowKind {
    Constructor { payload: Ty },
    Function { params: Vec<Ty> },
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::GenericParamDef, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct GenericParamDef {
    pub name: Symbol,
    pub def_id: DefId,
    pub index: u32,
    pub pure_wrt_drop: bool,
    pub kind: GenericParamDefKind,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::GenericParamDefKind, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum GenericParamDefKind {
    Lifetime,
    Type { has_default: bool, synthetic: bool },
    Const { has_default: bool },
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::Generics, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TyGenerics {
    pub parent: Option<DefId>,
    pub parent_count: usize,
    pub params: Vec<GenericParamDef>,
    // pub param_def_id_to_index: FxHashMap<DefId, u32>,
    pub has_self: bool,
    pub has_late_bound_regions: Option<Span>,
}

fn arrow_of_sig<'tcx, S: BaseState<'tcx>>(
    sig: &rustc_middle::ty::PolyFnSig<'tcx>,
    state: &S,
) -> Ty {
    let tcx = state.tcx();
    let ret: rustc_middle::ty::Ty = tcx.erase_late_bound_regions(sig.output());
    let inputs = sig.inputs();
    let indexes = inputs.skip_binder().iter().enumerate().map(|(i, _)| i);
    let params = indexes.map(|i| inputs.map_bound(|tys| tys[i]));
    let params: Vec<rustc_middle::ty::Ty> =
        params.map(|i| tcx.erase_late_bound_regions(i)).collect();
    Ty::Arrow {
        params: params.sinto(state),
        ret: ret.sinto(state),
    }
}

fn scalar_int_to_literal<'tcx, S: BaseState<'tcx>>(
    s: &S,
    x: rustc_middle::ty::ScalarInt,
    ty: rustc_middle::ty::Ty,
) -> LitKind {
    use rustc_middle::ty;
    match ty.kind() {
        ty::Char => LitKind::Char(
            x.try_to_u8()
                .expect("scalar_int_to_literal: expected a char")
                .into(),
        ),
        ty::Bool => LitKind::Bool(
            x.try_to_bool()
                .expect("scalar_int_to_literal: expected a bool"),
        ),
        ty::Int(kind) => LitKind::Int(x.assert_bits(x.size()), LitIntType::Signed(kind.sinto(s))),
        ty::Uint(kind) => {
            LitKind::Int(x.assert_bits(x.size()), LitIntType::Unsigned(kind.sinto(s)))
        }
        _ => panic!("scalar_int_to_literal: the type {:?} is not a literal", ty),
    }
}
fn const_to_expr<'tcx, S: BaseState<'tcx>>(
    s: &S,
    c: rustc_middle::ty::Const<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    span: rustc_span::Span,
) -> Expr {
    use rustc_middle::ty;
    let kind = match c.kind() {
        ty::ConstKind::Param(p) => ExprKind::ConstRef { id: p.sinto(s) },
        ty::ConstKind::Infer(..) => panic!("ty::ConstKind::Infer node? {:#?}", c),
        ty::ConstKind::Unevaluated(..) => panic!("ty::ConstKind::Unevaluated node? {:#?}", c),
        ty::ConstKind::Value(valtree) => return valtree_to_expr(s, valtree, ty, span),
        ty::ConstKind::Error(valtree) => panic!(),
        ty::ConstKind::Expr(e) => {
            use rustc_middle::ty::Expr as CE;
            panic!("ty::ConstKind::Expr {:#?}", e)
        }
        _ => panic!(),
    };
    Decorated {
        ty: ty.sinto(s),
        span: span.sinto(s),
        contents: Box::new(kind),
        hir_id: None,
        attributes: vec![],
    }
}
fn valtree_to_expr<'tcx, S: BaseState<'tcx>>(
    s: &S,
    valtree: rustc_middle::ty::ValTree<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    span: rustc_span::Span,
) -> Expr {
    use rustc_middle::ty;
    let kind = match (valtree, ty.kind()) {
        (_, ty::Ref(_, inner_ty, _)) => ExprKind::Borrow {
            borrow_kind: BorrowKind::Shared,
            arg: valtree_to_expr(s, valtree, *inner_ty, span),
        },
        (ty::ValTree::Branch(_), ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) => {
            let contents: rustc_middle::ty::DestructuredConst = s
                .tcx()
                .destructure_const(s.tcx().mk_const(valtree.clone(), ty));
            let fields = contents.fields.iter().copied();
            match ty.kind() {
                ty::Array(inner_ty, _) => ExprKind::Array {
                    fields: fields
                        .map(|field| const_to_expr(s, field, *inner_ty, span))
                        .collect(),
                },
                ty::Tuple(typs) => ExprKind::Tuple {
                    fields: fields
                        .zip(typs.into_iter())
                        .map(|(field, inner_ty)| const_to_expr(s, field, inner_ty, span))
                        .collect(),
                },
                ty::Adt(def, substs) => {
                    let variant_idx = contents
                        .variant
                        .expect("destructed const of adt without variant idx");
                    let variant_def = &def.variant(variant_idx);
                    ExprKind::Adt(AdtExpr {
                        info: get_variant_information(def, &variant_def.def_id, s),
                        user_ty: None,
                        fields: fields
                            .zip(&variant_def.fields)
                            .map(|(value, field)| FieldExpr {
                                field: field.did.sinto(s),
                                value: const_to_expr(s, value, field.ty(s.tcx(), substs), span),
                            })
                            .collect(),
                        base: None,
                    })
                }
                _ => unreachable!(),
            }
        }
        (ty::ValTree::Leaf(x), _) => ExprKind::Literal {
            lit: Spanned {
                node: scalar_int_to_literal(s, x, ty),
                span: rustc_span::DUMMY_SP.sinto(s),
            },
            neg: false,
        },
        _ => s.tcx().sess.span_fatal(
            span,
            format!(
                "valtree_to_expr: cannot handle valtree{:#?} ty={:#?}",
                valtree, ty
            ),
        ),
    };

    Decorated {
        ty: ty.sinto(s),
        span: span.sinto(s),
        contents: Box::new(kind),
        hir_id: None,
        attributes: vec![],
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::sty::AliasKind, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum AliasKind {
    Projection,
    Inherent,
    Opaque,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::TyKind<'tcx>, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Ty {
    Bool,

    /// The primitive character type; holds a Unicode scalar value
    /// (a non-surrogate code point). Written as `char`.
    Char,

    /// A primitive signed integer type. For example, `i32`.
    Int(IntTy),

    /// A primitive unsigned integer type. For example, `u32`.
    Uint(UintTy),

    /// A primitive floating-point type. For example, `f64`.
    Float(FloatTy),

    #[custom_arm(
        rustc_middle::ty::TyKind::FnPtr(sig) => arrow_of_sig(sig, state),
        x @ rustc_middle::ty::TyKind::FnDef(def, substs) => {
            let tcx = state.tcx();
            arrow_of_sig(&tcx.fn_sig(*def).subst(tcx, substs), state)
        },
        FROM_TYPE::Closure (defid, substs) => {
            let sig = substs.as_closure().sig();
            let sig = state.tcx().signature_unclosure(sig, rustc_hir::Unsafety::Normal);
            arrow_of_sig(&sig, state)
        },
    )]
    Arrow {
        params: Vec<Ty>,
        ret: Box<Ty>,
    },

    #[custom_arm(
        rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
            let def_id = adt_def.did().sinto(state);
            let generic_args: Vec<GenericArg> = substs.sinto(state);
            Ty::NamedType { def_id, generic_args }
        },
    )]
    NamedType {
        generic_args: Vec<GenericArg>,
        def_id: DefId,
    },

    /*
    /// Algebraic data types (ADT). For example: structures, enumerations and unions.
    ///
    /// For example, the type `List<i32>` would be represented using the `AdtDef`
    /// for `struct List<T>` and the substs `[i32]`.
    ///
    /// Note that generic parameters in fields only get lazily substituted
    /// by using something like `adt_def.all_fields().map(|field| field.ty(tcx, substs))`.
    Adt(x: AdtDef, y: Vec<GenericArg>),
     */
    /// An unsized FFI type that is opaque to Rust. Written as `extern type T`.
    Foreign(DefId),

    /// The pointee of a string slice. Written as `str`.
    Str,

    /// An array with the given length. Written as `[T; N]`.
    Array(Box<Ty>, Const),

    /// The pointee of an array slice. Written as `[T]`.
    Slice(Box<Ty>),

    /// A raw pointer. Written as `*mut T` or `*const T`
    RawPtr(TypeAndMut),

    /// A reference; a pointer with an associated lifetime. Written as
    /// `&'a mut T` or `&'a T`.
    Ref(Region, Box<Ty>, Mutability),

    // /// The anonymous type of a function declaration/definition. Each
    // /// function has a unique type.
    // ///
    // /// For the function `fn foo() -> i32 { 3 }` this type would be
    // /// shown to the user as `fn() -> i32 {foo}`.
    // ///
    // /// For example the type of `bar` here:
    // /// ```rust
    // /// fn foo() -> i32 { 1 }
    // /// let bar = foo; // bar: fn() -> i32 {foo}
    // /// ```
    // FnDef(d: DefId, r: Vec<GenericArg>),

    // /// A pointer to a function. Written as `fn() -> i32`.
    // ///
    // /// Note that both functions and closures start out as either
    // /// [FnDef] or [Closure] which can be then be coerced to this variant.
    // ///
    // /// For example the type of `bar` here:
    // ///
    // /// ```rust
    // /// fn foo() -> i32 { 1 }
    // /// let bar: fn() -> i32 = foo;
    // /// ```
    // FnPtr(x: PolyFnSig),
    /// A trait object. Written as `dyn for<'b> Trait<'b, Assoc = u32> + Send + 'a`.
    Dynamic(Vec<Binder<ExistentialPredicate>>, Region, DynKind),

    // /// The anonymous type of a closure. Used to represent the type of `|a| a`.
    // ///
    // /// Closure substs contain both the - potentially substituted - generic parameters
    // /// of its parent and some synthetic parameters. See the documentation for
    // /// `ClosureSubsts` for more details.
    // Closure(DefId, Vec<GenericArg>),
    /// The anonymous type of a generator. Used to represent the type of
    /// `|a| yield a`.
    ///
    /// For more info about generator substs, visit the documentation for
    /// `GeneratorSubsts`.
    Generator(DefId, Vec<GenericArg>, Movability),

    /*
    /// A type representing the types stored inside a generator.
    /// This should only appear as part of the `GeneratorSubsts`.
    ///
    /// Note that the captured variables for generators are stored separately
    /// using a tuple in the same way as for closures.
    ///
    /// Unlike upvars, the witness can reference lifetimes from
    /// inside of the generator itself. To deal with them in
    /// the type of the generator, we convert them to higher ranked
    /// lifetimes bound by the witness itself.
    ///
    /// Looking at the following example, the witness for this generator
    /// may end up as something like `for<'a> [Vec<i32>, &'a Vec<i32>]`:
    ///
    /// ```ignore UNSOLVED (ask @compiler-errors, should this error? can we just swap the yields?)
    /// #![feature(generators)]
    /// |a| {
    ///     let x = &vec![3];
    ///     yield a;
    ///     yield x[0];
    /// }
    /// # ;
    /// ```
     */
    // GeneratorWitness(Binder<Vec<Ty>>) use {
    //     rustc_middle::ty::TyKind::GeneratorWitness(b) => {

    //         Ty::GeneratorWitness(
    //             None // TODO
    //             // b.map_bound::<>(|x| x.sinto(state)).sinto(state)
    //         )
    //     }
    // },
    /// The never type `!`.
    Never,

    /// A tuple type. For example, `(i32, bool)`.
    Tuple(Vec<Ty>),

    Alias(AliasKind, AliasTy),

    /// A type parameter; for example, `T` in `fn f<T>(x: T) {}`.
    Param(ParamTy),

    /// Bound type variable, used to represent the `'a` in `for<'a> fn(&'a ())`.
    ///
    /// For canonical queries, we replace inference variables with bound variables,
    /// so e.g. when checking whether `&'_ (): Trait<_>` holds, we canonicalize that to
    /// `for<'a, T> &'a (): Trait<T>` and then convert the introduced bound variables
    /// back to inference variables in a new inference context when inside of the query.
    ///
    /// See the `rustc-dev-guide` for more details about
    /// [higher-ranked trait bounds][1] and [canonical queries][2].
    ///
    /// [1]: https://rustc-dev-guide.rust-lang.org/traits/hrtb.html
    /// [2]: https://rustc-dev-guide.rust-lang.org/traits/canonical-queries.html
    Bound(DebruijnIndex, BoundTy),

    /// A placeholder type, used during higher ranked subtyping to instantiate
    /// bound variables.
    Placeholder(PlaceholderType),

    /// A type variable used during type checking.
    ///
    /// Similar to placeholders, inference variables also live in a universe to
    /// correctly deal with higher ranked types. Though unlike placeholders,
    /// that universe is stored in the `InferCtxt` instead of directly
    /// inside of the type.
    Infer(InferTy),

    /// A placeholder for a type which could not be computed; this is
    /// propagated to avoid useless error messages.
    #[custom_arm(rustc_middle::ty::TyKind::Error(..) => Ty::Error,)]
    Error,

    #[todo]
    Todo(String),
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::StmtKind<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum StmtKind {
    Expr {
        scope: Scope,
        expr: Expr,
    },
    Let {
        remainder_scope: Scope,
        init_scope: Scope,
        pattern: Pat,
        initializer: Option<Expr>,
        else_block: Option<Block>,
        lint_level: LintLevel,
        #[not_in_source]
        #[map(attribute_from_scope(gstate, init_scope).1)]
        attributes: Vec<Attribute>,
    },
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::Variance, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Variance {
    Covariant,
    Invariant,
    Contravariant,
    Bivariant,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::CanonicalUserTypeAnnotation<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct CanonicalUserTypeAnnotation {
    pub user_ty: CanonicalUserType,
    pub span: Span,
    pub inferred_ty: Ty,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::Ascription<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Ascription {
    pub annotation: CanonicalUserTypeAnnotation,
    pub variance: Variance,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::RangeEnd, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum RangeEnd {
    Included,
    Excluded,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::PatRange<'tcx>, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct PatRange {
    pub lo: ConstantKind,
    pub hi: ConstantKind,
    pub end: RangeEnd,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct VariantInformations {
    constructs_record: bool, // Is a *non-tuple* struct
    constructs_type: DefId,
    type_namespace: DefId,
    variant: DefId,
}

trait IsRecord {
    fn is_record(&self) -> bool;
}
impl<'tcx> IsRecord for rustc_middle::ty::AdtDef<'tcx> {
    fn is_record(&self) -> bool {
        self.is_struct()
            && self
                .all_fields()
                .all(|field| field.name.to_ident_string().parse::<u64>().is_err())
    }
}

fn get_variant_information<'s, S: BaseState<'s>>(
    adt_def: &rustc_middle::ty::AdtDef<'s>,
    variant: &rustc_hir::def_id::DefId,
    s: &S,
) -> VariantInformations {
    let constructs_type = adt_def.did().sinto(s);
    VariantInformations {
        constructs_record: adt_def.is_record(),
        constructs_type: constructs_type.clone(),
        variant: variant.sinto(s),
        type_namespace: DefId {
            path: match constructs_type.path.as_slice() {
                [init @ .., _] => init.to_vec(),
                _ => panic!("Type {:#?} appears to have no path", constructs_type),
            },
            ..constructs_type.clone()
        },
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct AdtExpr {
    pub info: VariantInformations,
    pub user_ty: Option<CanonicalUserType>,
    pub fields: Vec<FieldExpr>,
    pub base: Option<FruInfo>,
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::PatKind<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[append(rustc_middle::thir::PatKind::Leaf {..} => panic!("PatKind::Leaf: should never come up"),)]
pub enum PatKind {
    /// A wildcard pattern: `_`.
    Wild,

    AscribeUserType {
        ascription: Ascription,
        subpattern: Pat,
    },

    #[custom_arm(
        rustc_middle::thir::PatKind::Binding {mutability, name, mode, var, ty, subpattern, is_primary} => {
            let local_ctx = gstate.local_ctx();
            local_ctx.borrow_mut().vars.insert(var.clone(), name.to_string());
            PatKind::Binding {
                mutability: mutability.sinto(gstate),
                mode: mode.sinto(gstate),
                var: var.sinto(gstate),
                ty: ty.sinto(gstate),
                subpattern: subpattern.sinto(gstate),
                is_primary: is_primary.sinto(gstate),
            }
        }
    )]
    /// `x`, `ref x`, `x @ P`, etc.
    Binding {
        mutability: Mutability,
        mode: BindingMode,
        var: LocalIdent, // name VS var? TODO
        ty: Ty,
        subpattern: Option<Pat>,
        /// Is this the leftmost occurrence of the binding, i.e., is `var` the
        /// `HirId` of this pattern?
        is_primary: bool,
    },
    #[custom_arm(
        FROM_TYPE::Variant {adt_def, variant_index, substs, subpatterns} => {
            let variants = adt_def.variants();
            let variant: &rustc_middle::ty::VariantDef = &variants[variant_index.clone()];
            TO_TYPE::Variant {
                info: get_variant_information(adt_def, &variant.def_id, gstate),
                subpatterns: subpatterns
                    .iter()
                    .map(|f| FieldPat {
                        field: variant.fields[f.field].did.sinto(gstate),
                        pattern: f.pattern.sinto(gstate),
                    })
                    .collect(),
                substs: substs.sinto(gstate),
            }
        }
    )]
    /// Any variant, TODO rename into constructor?
    Variant {
        info: VariantInformations,
        // constructs_record: bool,
        // constructs_type: DefId,
        // type_namespace: DefId,
        // variant: DefId,
        substs: Vec<GenericArg>,
        subpatterns: Vec<FieldPat>,
    },
    #[disable_mapping]
    Tuple {
        subpatterns: Vec<Pat>,
    },
    /// `box P`, `&P`, `&mut P`, etc.
    Deref {
        subpattern: Pat,
    },

    /// One of the following:
    /// * `&str`, which will be handled as a string pattern and thus exhaustiveness
    ///   checking will detect if you use the same string twice in different patterns.
    /// * integer, bool, char or float, which will be handled by exhaustiveness to cover exactly
    ///   its own value, similar to `&str`, but these values are much simpler.
    /// * Opaque constants, that must not be matched structurally. So anything that does not derive
    ///   `PartialEq` and `Eq`.
    Constant {
        value: ConstantKind,
    },

    Range(PatRange),
    /// Matches against a slice, checking the length and extracting elements.
    /// irrefutable when there is a slice pattern and both `prefix` and `suffix` are empty.
    /// e.g., `&[ref xs @ ..]`.
    Slice {
        prefix: Vec<Pat>,
        slice: Option<Pat>,
        suffix: Vec<Pat>,
    },

    /// Fixed match against an array; irrefutable.
    Array {
        prefix: Vec<Pat>,
        slice: Option<Pat>,
        suffix: Vec<Pat>,
    },

    /// An or-pattern, e.g. `p | q`.
    /// Invariant: `pats.len() >= 2`.
    Or {
        pats: Vec<Pat>,
    },
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Guard<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Guard {
    If(Expr),
    IfLet(Pat, Expr),
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Arm<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Arm {
    pub pattern: Pat,
    pub guard: Option<Guard>,
    pub body: Expr,
    pub lint_level: LintLevel,
    pub scope: Scope,
    pub span: Span,
    #[not_in_source]
    #[map(attribute_from_scope(gstate, scope).1)]
    attributes: Vec<Attribute>,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::Unsafety, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Unsafety {
    Unsafe,
    Normal,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::adjustment::PointerCast, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum PointerCast {
    ReifyFnPointer,
    UnsafeFnPointer,
    ClosureFnPointer(Unsafety),
    MutToConstPointer,
    ArrayToPointer,
    Unsize,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::mir::BorrowKind, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum BorrowKind {
    Shared,
    Shallow,
    Unique,
    Mut { allow_two_phase_borrow: bool },
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::StrStyle, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum StrStyle {
    Cooked,
    Raw(u8),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_ast::ast::LitKind, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum LitKind {
    Str(Symbol, StrStyle),
    ByteStr(Vec<u8>, StrStyle),
    CStr(Vec<u8>, StrStyle),
    Byte(u8),
    Char(char),
    Int(u128, LitIntType),
    Float(Symbol, LitFloatType),
    Bool(bool),
    Err,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct MacroInvokation {
    pub macro_ident: DefId,
    pub argument: String,
    pub span: Span,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::ImplicitSelfKind, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ImplicitSelfKind {
    Imm,
    Mut,
    ImmRef,
    MutRef,
    None,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::CommentKind, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum CommentKind {
    Line,
    Block,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::AttrArgs, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum AttrArgs {
    Empty,
    Delimited(DelimArgs),

    #[todo]
    Todo(String),
    // Eq(Span, AttrArgsEq),
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::AttrItem, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct AttrItem {
    #[map(rustc_ast_pretty::pprust::path_to_string(x))]
    pub path: String,
    pub args: AttrArgs,
    pub tokens: Option<TokenStream>,
}

impl<S> SInto<S, String> for rustc_ast::tokenstream::LazyAttrTokenStream {
    fn sinto(&self, st: &S) -> String {
        self.to_attr_token_stream().to_tokenstream().sinto(st)
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::NormalAttr, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct NormalAttr {
    pub item: AttrItem,
    pub tokens: Option<TokenStream>,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::AttrKind, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum AttrKind {
    Normal(NormalAttr),
    DocComment(CommentKind, Symbol),
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Param<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Param {
    pub pat: Option<Pat>,
    pub ty: Ty,
    pub ty_span: Option<Span>,
    pub self_kind: Option<ImplicitSelfKind>,
    pub hir_id: Option<HirId>,
    #[not_in_source]
    #[map(hir_id.map(|id| {
        s.tcx().hir().attrs(id).sinto(s)
    }).unwrap_or(vec![]))]
    pub attributes: Vec<Attribute>,
}

pub type Body = Expr;
pub fn inspect_local_def_id<'tcx, S: BaseState<'tcx>>(
    did: rustc_hir::def_id::LocalDefId,
    owner_id: rustc_hir::hir_id::OwnerId,
    s: &S,
) -> (rustc_middle::thir::Thir<'tcx>, Vec<Param>, Body) {
    let tcx: rustc_middle::ty::TyCtxt = s.tcx();
    let thirs = s.cached_thirs();

    let (thir, expr) = thirs
        .get(&did)
        .unwrap_or_else(|| panic!("Could not load body for id {did:?}"));

    let s = State {
        tcx: s.tcx(),
        options: s.options(),
        thir: thir.clone(),
        owner_id,
        opt_def_id: s.opt_def_id(),
        macro_infos: s.macro_infos(),
        local_ctx: s.local_ctx(),
        cached_thirs: s.cached_thirs(),
        exported_spans: s.exported_spans(),
    };
    let params: Vec<Param> = thir.params.iter().map(|x| x.sinto(&s)).collect();
    let body = expr.sinto(&s);
    (thir.clone(), params, body)
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::ExprKind<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[append(
    // rustc_middle::thir::ExprKind::Scope {region_scope, lint_level, value} => {
    //     gstate.thir().exprs[*value].clone().unroll_scope(gstate).sinto(gstate).kind
    // },
    rustc_middle::thir::ExprKind::Scope {..} => {
        panic!("Scope should have been eliminated at this point");
    },
    rustc_middle::thir::ExprKind::Field {..} => {
        panic!("Field should have been eliminated at this point");
    },
)]
pub enum ExprKind {
    // /// and to track the `HirId` of the expressions within the scope.
    // Scope {
    //     region_scope: Scope,
    //     lint_level: LintLevel,
    //     value: Expr,
    // },
    /// A `box <value>` expression.
    Box {
        value: Expr,
    },
    /// TODO
    #[disable_mapping]
    MacroInvokation(MacroInvokation),
    /// An `if` expression.
    If {
        if_then_scope: Scope,
        cond: Expr,
        then: Expr,
        else_opt: Option<Expr>,
    },

    /// A function call. Method calls and overloaded operators are converted to plain function calls.
    #[map({
        let e = gstate.thir().exprs[*fun].unroll_scope(gstate);
        let (def, substs) = match &e.kind {
            rustc_middle::thir::ExprKind::ZstLiteral {user_ty: _ /* TODO: see whether this is relevant or not */} => {
                match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(def, substs) =>
                        (def, substs),
                    ty_kind => {
                        supposely_unreachable!(
                            "CallNotTyFnDef":
                            e, ty_kind
                        );
                        panic!();
                    }
                }
            },
            kind => {
                supposely_unreachable!(
                    "CallNotZstLiteral":
                    e, kind
                );
                panic!();
            }
        };
        let tcx = gstate.tcx();
        match tcx.trait_of_item(*def) {
            Some(trait_def_id) => {
                // println!("########################");
                // println!("expr={:#?}", self);
                // printlnresolve!("x={:#?}", x);
                // resolve_trait(
                //     rustc_middle::ty::TraitRef::new(trait_def_id, substs),
                //     gstate
                // );
                ()
            },
            None => ()
        }
        // if false {
        //     let tcx = gstate.tcx();
        //     let g = tcx.generics_of(def);
        //     let g = tcx.predicates_of(def);
        //     let g = g.parent.unwrap();
        //     let g = tcx.predicates_of(g);
        //     panic!("generics={:#?}", g);
        // }
        TO_TYPE::Call {
            ty: ty.sinto(gstate),
            args: args.sinto(gstate),
            from_hir_call: from_hir_call.sinto(gstate),
            fn_span: fn_span.sinto(gstate),
            fun: Expr {
                contents: Box::new(ExprKind::GlobalName {
                    id: def.sinto(gstate)
                }),
                span: e.span.sinto(gstate),
                ty: e.ty.sinto(gstate),
                hir_id: None, /* Todo: this is incorrect */
                attributes: vec![],
            },
        }
    })]
    Call {
        /// The type of the function. This is often a [`FnDef`] or a [`FnPtr`].
        ///
        /// [`FnDef`]: ty::TyKind::FnDef
        /// [`FnPtr`]: ty::TyKind::FnPtr
        ty: Ty,
        /// The function itself.
        fun: Expr, // TODO: can [ty] and [fun.ty] be different?
        /// The arguments passed to the function.
        ///
        /// Note: in some cases (like calling a closure), the function call `f(...args)` gets
        /// rewritten as a call to a function trait method (e.g. `FnOnce::call_once(f, (...args))`).
        args: Vec<Expr>,
        /// Whether this is from an overloaded operator rather than a
        /// function call from HIR. `true` for overloaded function call.
        from_hir_call: bool,
        /// The span of the function, without the dot and receiver
        /// (e.g. `foo(a, b)` in `x.foo(a, b)`).
        fn_span: Span,
    },
    /// A *non-overloaded* dereference.
    Deref {
        arg: Expr,
    },
    /// A *non-overloaded* binary operation.
    Binary {
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
    },
    LogicalOp {
        op: LogicalOp,
        lhs: Expr,
        rhs: Expr,
    },
    /// A *non-overloaded* unary operation. Note that here the deref (`*`)
    /// operator is represented by `ExprKind::Deref`.
    Unary {
        op: UnOp,
        arg: Expr,
    },
    /// A cast: `<source> as <type>`. The type we cast to is the type of
    /// the parent expression.
    Cast {
        source: Expr,
    },
    Use {
        // TODO: what is Use?
        // #[map({supposely_unreachable!("Expr::Use": self); panic!()})]
        source: Expr,
    }, // Use a lexpr to get a vexpr.
    /// A coercion from `!` to any type.
    NeverToAny {
        source: Expr,
    },
    /// A pointer cast. More information can be found in [`PointerCast`].
    Pointer {
        cast: PointerCast,
        source: Expr,
    },
    /// A `loop` expression.
    Loop {
        body: Expr,
    },
    /// A `match` expression.
    Match {
        scrutinee: Expr,
        arms: Vec<Arm>,
    },
    Let {
        // Is [Let] only for [if let _ = ... {}...]?
        expr: Expr,
        pat: Pat,
    },
    #[custom_arm(
        rustc_middle::thir::ExprKind::Block { block: block_id } => {
            let block = gstate.thir().blocks[block_id.clone()].clone();
            match (block.stmts, block.expr, block.safety_mode, block.targeted_by_break) {
                (box [], Some(e), rustc_middle::thir::BlockSafety::Safe, false) =>
                    *e.sinto(gstate).contents,
                _ => ExprKind::Block {
                    block: block_id.sinto(gstate)
                }
            }
        },
    )]
    /// A block.
    Block {
        #[serde(flatten)]
        block: Block,
    },
    /// A *non-overloaded* operation assignment, e.g. `lhs += rhs`.
    Assign {
        lhs: Expr,
        rhs: Expr,
    },
    AssignOp {
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
    },
    /// Access to a field of a struct, an union, or an enum.
    #[disable_mapping]
    Field {
        field: DefId,
        lhs: Expr,
    },

    #[disable_mapping]
    TupleField {
        field: usize,
        lhs: Expr,
    },

    // use {
    //         rustc_middle::thir::ExprKind::Field {lhs, variant_index, name} => {
    //             let lhs = lhs.sinto(gstate);
    //             let variant_index = variant_index.sinto(gstate);
    //             let name = name.sinto(gstate);
    //             if variant_index > 0 {
    //                 panic!("FIELD: {}, {:#?}", name, lhs.span);
    //             }
    //             ExprKind::Field {lhs, variant_index, name}
    //         }
    //     },
    /// A *non-overloaded* indexing operation.
    Index {
        lhs: Expr,
        index: Expr,
    },
    /// A local variable.
    VarRef {
        id: LocalIdent,
    },

    #[disable_mapping]
    /// A local (const) variable.
    ConstRef {
        id: ParamConst,
    },

    #[disable_mapping]
    GlobalName {
        id: GlobalIdent,
    },
    // TODO
    /// Used to represent upvars mentioned in a closure/generator
    UpvarRef {
        /// DefId of the closure/generator
        closure_def_id: DefId,

        /// HirId of the root variable
        var_hir_id: LocalIdent,
    },
    /// A borrow, e.g. `&arg`.
    Borrow {
        borrow_kind: BorrowKind,
        arg: Expr,
    },
    /// A `&raw [const|mut] $place_expr` raw borrow resulting in type `*[const|mut] T`.
    AddressOf {
        #[map(panic!("AddressOf"))]
        mutability: Mutability,
        arg: Expr,
    },
    /// A `break` expression.
    Break {
        label: Scope,
        value: Option<Expr>,
    },
    /// A `continue` expression.
    Continue {
        label: Scope,
    },
    /// A `return` expression.
    Return {
        value: Option<Expr>,
    },
    /// An inline `const` block, e.g. `const {}`.
    ConstBlock {
        did: DefId,
        substs: Vec<GenericArg>,
    },
    /// An array literal constructed from one repeated element, e.g. `[1; 5]`.
    Repeat {
        value: Expr,
        count: Const,
    },
    /// An array, e.g. `[a, b, c, d]`.
    Array {
        fields: Vec<Expr>,
    },
    /// A tuple, e.g. `(a, b, c, d)`.
    Tuple {
        fields: Vec<Expr>,
    },
    /// An ADT constructor, e.g. `Foo {x: 1, y: 2}`.
    Adt(AdtExpr),
    /// A type ascription on a place.
    PlaceTypeAscription {
        source: Expr,
        /// Type that the user gave to this expression
        user_ty: Option<CanonicalUserType>,
    },
    /// A type ascription on a value, e.g. `42: i32`.
    ValueTypeAscription {
        source: Expr,
        /// Type that the user gave to this expression
        user_ty: Option<CanonicalUserType>,
    },
    /// A closure definition.
    #[custom_arm(FROM_TYPE::Closure(e) => {
        let (_, params, body) = inspect_local_def_id(e.closure_id, gstate.owner_id(), gstate);
        TO_TYPE::Closure {
            params,
            body,
            upvars: e.upvars.sinto(gstate),
            movability: e.movability.sinto(gstate)
        }
    },
    )]
    Closure {
        params: Vec<Param>,
        body: Body,
        upvars: Vec<Expr>,
        movability: Option<Movability>,
    },
    /// A literal.
    Literal {
        lit: Spanned<LitKind>,
        neg: bool, // TODO
    },
    /// For literals that don't correspond to anything in the HIR
    NonHirLiteral {
        lit: ScalarInt,
        user_ty: Option<CanonicalUserType>,
    },
    /// A literal of a ZST type.
    //zero space type
    // This is basically used for functions! e.g. `<T>::from`
    ZstLiteral {
        user_ty: Option<CanonicalUserType>,
    },
    /// Associated constants and named constants
    NamedConst {
        def_id: GlobalIdent,
        substs: Vec<GenericArg>,
        user_ty: Option<CanonicalUserType>,
    },
    ConstParam {
        param: ParamConst,
        def_id: GlobalIdent,
    },
    // FIXME improve docs for `StaticRef` by distinguishing it from `NamedConst`
    /// A literal containing the address of a `static`.
    ///
    /// This is only distinguished from `Literal` so that we can register some
    /// info for diagnostics.
    StaticRef {
        alloc_id: u64,
        ty: Ty,
        def_id: GlobalIdent,
    },
    // /// Inline assembly, i.e. `asm!()`.
    // InlineAsm {
    //     template: &'tcx [InlineAsmTemplatePiece],
    //     operands: Box<[InlineAsmOperand<'tcx>]>,
    //     options: InlineAsmOptions,
    //     line_spans: &'tcx [Span],
    // },
    // /// An expression taking a reference to a thread local.
    // ThreadLocalRef(DefId),
    /// A `yield` expression.
    Yield {
        value: Expr,
    },
    #[todo]
    Todo(String),
}

pub trait ExprKindExt<'tcx> {
    fn unroll_scope<S: IsState<'tcx> + HasThir<'tcx>>(
        &self,
        s: &S,
    ) -> rustc_middle::thir::Expr<'tcx>;
}

impl<'tcx> ExprKindExt<'tcx> for rustc_middle::thir::Expr<'tcx> {
    fn unroll_scope<S: IsState<'tcx> + HasThir<'tcx>>(
        &self,
        s: &S,
    ) -> rustc_middle::thir::Expr<'tcx> {
        // TODO: when we see a loop, we should lookup its label! label is actually a scope id
        // we remove scopes here, whence the TODO
        match self.kind {
            rustc_middle::thir::ExprKind::Scope {
                region_scope,
                lint_level,
                value,
            } => s.thir().exprs[value].unroll_scope(s),
            _ => self.clone(),
        }
    }
}
