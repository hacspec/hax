use crate::prelude::*;

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'a, S: BaseState<'a>>, from: rustc_hir::definitions::DisambiguatedDefPathData, state: S as s)]
pub struct DisambiguatedDefPathItem {
    pub data: DefPathItem,
    pub disambiguator: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct DefId {
    pub krate: String,
    pub path: Vec<DisambiguatedDefPathItem>,
}

impl<'s, S: BaseState<'s>> SInto<S, DefId> for rustc_hir::def_id::DefId {
    fn sinto(&self, s: &S) -> DefId {
        let tcx = s.base().tcx;
        let def_path = tcx.def_path(self.clone());
        let krate = tcx.crate_name(def_path.krate);
        DefId {
            path: def_path.data.iter().map(|x| x.sinto(s)).collect(),
            krate: format!("{}", krate),
        }
    }
}

impl std::convert::From<DefId> for Path {
    fn from(v: DefId) -> Vec<String> {
        std::iter::once(v.krate)
            .chain(v.path.into_iter().filter_map(|item| match item.data {
                DefPathItem::TypeNs(s)
                | DefPathItem::ValueNs(s)
                | DefPathItem::MacroNs(s)
                | DefPathItem::LifetimeNs(s) => Some(s),
                _ => None,
            }))
            .collect()
    }
}

pub type GlobalIdent = DefId;
impl<'tcx, S: BaseState<'tcx>> SInto<S, GlobalIdent> for rustc_hir::def_id::LocalDefId {
    fn sinto(&self, st: &S) -> DefId {
        self.to_def_id().sinto(st)
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'a, S>, from: rustc_middle::thir::LogicalOp, state: S as _s)]
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

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'slt, S: BaseState<'slt> + HasThir<'slt>>, from: rustc_middle::thir::LintLevel, state: S as gstate)]
pub enum LintLevel {
    Inherited,
    Explicit(HirId),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_ast::ast::AttrStyle, state: S as _s)]
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
#[args(<'slt, S: BaseState<'slt>>, from: rustc_middle::mir::UnOp, state: S as _s)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'slt, S: BaseState<'slt>>, from: rustc_middle::mir::BinOp, state: S as _s)]
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

        match self.eval(s.base().tcx, get_param_env(s)) {
            RustConstantKind::Val(const_value, ty) => {
                use rustc_middle::mir::interpret::ConstValue;
                match const_value {
                    ConstValue::Scalar(scalar) => ConstantKind::Lit(scalar_int_to_lit_kind(
                        s,
                        scalar.assert_int(),
                        ty.clone(),
                    )),
                    _ => ConstantKind::Todo(format!("{:#?}", self)),
                }
            }
            RustConstantKind::Ty(c) => match c.sinto(s).unwrap_borrow() {
                Decorated {
                    contents:
                        box ExprKind::Literal {
                            lit: Spanned { node, .. },
                            ..
                        },
                    ..
                } => ConstantKind::Lit(node),
                e => ConstantKind::Ty(Box::new(e)),
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

impl<S> SInto<S, u64> for rustc_middle::mir::interpret::AllocId {
    fn sinto(&self, _: &S) -> u64 {
        self.0.get()
    }
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, Box<Ty>> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Box<Ty> {
        Box::new(self.sinto(s))
    }
}

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
#[args(<'tcx, S>, from: rustc_hir::Movability, state: S as _s)]
pub enum Movability {
    Static,
    Movable,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalTyVarKind, state: S as gstate)]
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
#[args(<S>, from: rustc_middle::ty::DynKind, state: S as _s)]
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

impl<'tcx, S: BaseState<'tcx>, T: SInto<S, U>, U> SInto<S, Canonical<U>>
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
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalVarKind<'tcx>, state: S as gstate)]
pub enum CanonicalVarInfo {
    Ty(CanonicalTyVarKind),
    PlaceholderTy(PlaceholderType),
    Region(UniverseIndex),
    PlaceholderRegion(PlaceholderRegion),
    Const(UniverseIndex, Ty),
    PlaceholderConst(PlaceholderConst, Ty),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::subst::UserSelfTy<'tcx>, state: S as gstate)]
pub struct UserSelfTy {
    pub impl_def_id: DefId,
    pub self_ty: Ty,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::subst::UserSubsts<'tcx>, state: S as gstate)]
pub struct UserSubsts {
    pub substs: Vec<GenericArg>,
    pub user_self_ty: Option<UserSelfTy>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::UserType<'tcx>, state: S as _s)]
pub enum UserType {
    // TODO: for now, we don't use user types at all.
    // We disable it for now, since it cause the following to fail:
    //
    //    pub const MY_VAL: u16 = 5;
    //    pub type Alias = MyStruct<MY_VAL>; // Using the literal 5, it goes through
    //
    //    pub struct MyStruct<const VAL: u16> {}
    //
    //    impl<const VAL: u16> MyStruct<VAL> {
    //        pub const MY_CONST: u16 = VAL;
    //    }
    //
    //    pub fn do_something() -> u32 {
    //        u32::from(Alias::MY_CONST)
    //    }
    //
    // In this case, we get a [rustc_middle::ty::ConstKind::Bound] in
    // [do_something], which we are not able to translate.
    // See: https://github.com/hacspec/hacspec-v2/pull/209

    // Ty(Ty),
    // TypeOf(DefId, UserSubsts),
    #[todo]
    Todo(String),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_hir::def::CtorKind, state: S as _s)]
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

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::ty::VariantDef, state: S as state)]
pub struct VariantDef {
    pub def_id: DefId,
    pub ctor: Option<(CtorKind, DefId)>,
    pub name: Symbol,
    pub discr: VariantDiscr,
    #[map(fields.raw.sinto(state))]
    pub fields: Vec<FieldDef>,
}

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

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::FruInfo<'tcx>, state: S as gstate)]
/// This is [Constructor {⟨field_types⟩, ..base}]
pub struct FruInfo {
    pub base: Expr,
    pub field_types: Vec<Ty>,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct FieldExpr {
    pub field: DefId,
    pub value: Expr,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
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
    pub line: usize,
    pub col: usize,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::DesugaringKind, state: S as _s)]
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
#[args(<S>, from: rustc_span::hygiene::AstPass, state: S as _s)]
pub enum AstPass {
    StdImports,
    TestHarness,
    ProcMacroHarness,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_span::hygiene::MacroKind, state: S as _s)]
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
#[args(<S>, from: rustc_span::edition::Edition, state: S as _s)]
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
    pub lo: Loc,
    pub hi: Loc,
    pub filename: FileName,
    // expn_backtrace: Vec<ExpnData>,
}

impl Into<Loc> for rustc_span::Loc {
    fn into(self) -> Loc {
        Loc {
            line: self.line,
            col: self.col_display,
        }
    }
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, Span> for rustc_span::Span {
    fn sinto(&self, s: &S) -> Span {
        let set: crate::state::ExportedSpans = s.base().exported_spans;
        set.borrow_mut().insert(self.clone());
        translate_span(self.clone(), s.base().tcx.sess)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct LocalIdent {
    pub name: String,
    pub id: HirId,
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, LocalIdent> for rustc_middle::thir::LocalVarId {
    fn sinto(&self, s: &S) -> LocalIdent {
        LocalIdent {
            name: s
                .base()
                .local_ctx
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
    fn sinto(&self, _: &S) -> String {
        self.as_path().display().to_string()
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq, Hash)]
#[args(<S>, from: rustc_span::RealFileName, state: S as _s)]
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
    fn sinto(&self, _: &S) -> u64 {
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
#[args(<'tcx, S>, from: rustc_middle::thir::BlockSafety, state: S as _s)]
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
    pub trait_def_id: Option<DefId>,
    pub def_id: DefId,
}

impl<'tcx, S: BaseState<'tcx>> SInto<S, AliasTy> for rustc_middle::ty::AliasTy<'tcx> {
    fn sinto(&self, s: &S) -> AliasTy {
        let tcx = s.base().tcx;
        use rustc_hir::def::DefKind::*;
        let trait_def_id = matches!(
            tcx.def_kind(self.def_id),
            AssocTy | AssocConst | ImplTraitPlaceholder
        )
        .then(|| {
            let _trait_ref = self.trait_ref(tcx);
            self.trait_def_id(tcx).sinto(s)
        });
        AliasTy {
            substs: self.substs.sinto(s),
            trait_def_id,
            def_id: self.def_id.sinto(s),
        }
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::thir::BindingMode, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum BindingMode {
    ByValue,
    ByRef(BorrowKind),
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::Stmt<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Stmt {
    pub kind: StmtKind,
    pub opt_destruction_scope: Option<Scope>,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::MacDelimiter, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum MacDelimiter {
    Parenthesis,
    Bracket,
    Brace,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::Delimiter, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
    Invisible,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::tokenstream::TokenTree, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum TokenTree {
    Token(Token, Spacing),
    Delimited(DelimSpan, Delimiter, TokenStream),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::tokenstream::Spacing, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Spacing {
    Alone,
    Joint,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::BinOpToken, state: S as _s)]
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
    fn sinto(&self, _: &S) -> String {
        rustc_ast_pretty::pprust::tts_to_string(self)
    }
}

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

pub trait ExprState<'tcx> = BaseState<'tcx> + HasThir<'tcx> + HasOwnerId;

impl<'tcx, S: ExprState<'tcx>> SInto<S, Expr> for rustc_middle::thir::Expr<'tcx> {
    fn sinto(&self, s: &S) -> Expr {
        let (hir_id, attributes) = self.hir_id_and_attributes(s);
        let hir_id = hir_id.map(|hir_id| hir_id.index());
        let unrolled = self.unroll_scope(s);
        let rustc_middle::thir::Expr { span, kind, ty, .. } = unrolled;
        let contents = match macro_invocation_of_span(span, s).map(ExprKind::MacroInvokation) {
            Some(contents) => contents,
            None => match kind {
                rustc_middle::thir::ExprKind::NonHirLiteral { lit, .. } => ExprKind::Literal {
                    lit: Spanned {
                        node: scalar_int_to_lit_kind(s, lit, ty),
                        span: span.sinto(s),
                    },
                    neg: false,
                },
                rustc_middle::thir::ExprKind::ZstLiteral { .. } => match ty.kind() {
                    rustc_middle::ty::TyKind::FnDef(def, _substs) => {
                        /* TODO: translate substs
                        let tcx = s.base().tcx;
                        let sig = &tcx.fn_sig(*def).subst(tcx, substs);
                        let ret: rustc_middle::ty::Ty = tcx.erase_late_bound_regions(sig.output());
                        let inputs = sig.inputs();
                        let indexes = inputs.skip_binder().iter().enumerate().map(|(i, _)| i);
                        let params = indexes.map(|i| inputs.map_bound(|tys| tys[i]));
                        let params: Vec<rustc_middle::ty::Ty> =
                        params.map(|i| tcx.erase_late_bound_regions(i)).collect();
                        */
                        return Expr {
                            contents: Box::new(ExprKind::GlobalName { id: def.sinto(s) }),
                            span: self.span.sinto(s),
                            ty: ty.sinto(s),
                            hir_id,
                            attributes,
                        };
                    }
                    _ => {
                        if ty.is_phantom_data() {
                            let rustc_middle::ty::Adt(def, _) = ty.kind() else {
                                panic!()
                            };
                            let variant_id = rustc_abi::VariantIdx::from_u32(0);
                            let variant = def.variant(variant_id);
                            let adt_def = AdtExpr {
                                info: get_variant_information(def, &variant.def_id, s),
                                user_ty: None,
                                base: None,
                                fields: vec![],
                            };
                            return Expr {
                                contents: Box::new(ExprKind::Adt(adt_def)),
                                span: self.span.sinto(s),
                                ty: ty.sinto(s),
                                hir_id,
                                attributes,
                            };
                        } else {
                            supposely_unreachable!(
                                "ZstLiteral ty≠FnDef(...) or PhantomData": kind,
                                span,
                                ty
                            );
                            kind.sinto(s)
                        }
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
                        rustc_middle::ty::TyKind::Adt(adt_def, _substs) => {
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
                            fatal!(s, "ExprKindFieldBadTy")
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
                rustc_middle::ty::TyKind::Tuple(..) => PatKind::Tuple {
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
                    fatal!(s, "PatLeafNonAdtTy")
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
#[args(<S>, from: rustc_type_ir::IntTy, state: S as _s)]
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
#[args(<S>, from: rustc_type_ir::FloatTy, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum FloatTy {
    F32,
    F64,
}

impl<'tcx, S> SInto<S, FloatTy> for rustc_ast::ast::FloatTy {
    fn sinto(&self, _: &S) -> FloatTy {
        use rustc_ast::ast::FloatTy as T;
        match self {
            T::F32 => FloatTy::F32,
            T::F64 => FloatTy::F64,
        }
    }
}

impl<'tcx, S> SInto<S, IntTy> for rustc_ast::ast::IntTy {
    fn sinto(&self, _: &S) -> IntTy {
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
    fn sinto(&self, _: &S) -> UintTy {
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
#[args(<S>, from: rustc_type_ir::UintTy, state: S as _s)]
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

#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::sty::AliasKind, state: S as _s)]
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
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),

    #[custom_arm(
        rustc_middle::ty::TyKind::FnPtr(sig) => arrow_of_sig(sig, state),
        rustc_middle::ty::TyKind::FnDef(def, substs) => {
            let tcx = state.base().tcx;
            arrow_of_sig(&tcx.fn_sig(*def).subst(tcx, substs), state)
        },
        FROM_TYPE::Closure (_defid, substs) => {
            let sig = substs.as_closure().sig();
            let sig = state.base().tcx.signature_unclosure(sig, rustc_hir::Unsafety::Normal);
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
            Ty::Adt { def_id, generic_args }
        },
    )]
    Adt {
        generic_args: Vec<GenericArg>,
        def_id: DefId,
    },
    Foreign(DefId),
    Str,
    Array(Box<Ty>, Const),
    Slice(Box<Ty>),
    RawPtr(TypeAndMut),
    Ref(Region, Box<Ty>, Mutability),
    Dynamic(Vec<Binder<ExistentialPredicate>>, Region, DynKind),
    Generator(DefId, Vec<GenericArg>, Movability),
    Never,
    Tuple(Vec<Ty>),
    Alias(AliasKind, AliasTy),
    Param(ParamTy),
    Bound(DebruijnIndex, BoundTy),
    Placeholder(PlaceholderType),
    Infer(InferTy),
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
#[args(<S>, from: rustc_middle::ty::Variance, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Variance {
    Covariant,
    Invariant,
    Contravariant,
    Bivariant,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::CanonicalUserTypeAnnotation<'tcx>, state: S as gstate)]
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
#[args(<S>, from: rustc_hir::RangeEnd, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum RangeEnd {
    Included,
    Excluded,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasThir<'tcx>>, from: rustc_middle::thir::PatRange<'tcx>, state: S as state)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct PatRange {
    pub lo: TypedConstantKind,
    pub hi: TypedConstantKind,
    pub end: RangeEnd,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct VariantInformations {
    pub type_namespace: DefId,

    pub typ: DefId,
    pub variant: DefId,

    // A record type is a type with only one variant which is a record variant.
    pub typ_is_record: bool,
    // A record variant is a variant whose fields are named, a record
    // variant always has at least one field.
    pub variant_is_record: bool,
    // A struct is a type with exactly one variant. Note that one
    // variant is named exactly as the type.
    pub typ_is_struct: bool,
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
#[append(rustc_middle::thir::PatKind::Leaf {..} => fatal!(gstate, "PatKind::Leaf: should never come up"),)]
pub enum PatKind {
    Wild,
    AscribeUserType {
        ascription: Ascription,
        subpattern: Pat,
    },
    #[custom_arm(
        rustc_middle::thir::PatKind::Binding {mutability, name, mode, var, ty, subpattern, is_primary} => {
            let local_ctx = gstate.base().local_ctx;
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
    Binding {
        mutability: Mutability,
        mode: BindingMode,
        var: LocalIdent, // name VS var? TODO
        ty: Ty,
        subpattern: Option<Pat>,
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
    Deref {
        subpattern: Pat,
    },
    Constant {
        value: TypedConstantKind,
    },
    Range(PatRange),
    Slice {
        prefix: Vec<Pat>,
        slice: Option<Pat>,
        suffix: Vec<Pat>,
    },
    Array {
        prefix: Vec<Pat>,
        slice: Option<Pat>,
        suffix: Vec<Pat>,
    },
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
#[args(<S>, from: rustc_hir::Unsafety, state: S as _s)]
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
#[args(<S>, from: rustc_hir::ImplicitSelfKind, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ImplicitSelfKind {
    Imm,
    Mut,
    ImmRef,
    MutRef,
    None,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::CommentKind, state: S as _s)]
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
        s.base().tcx.hir().attrs(id).sinto(s)
    }).unwrap_or(vec![]))]
    pub attributes: Vec<Attribute>,
}

#[derive(AdtInto)]
#[args(<'tcx, S: ExprState<'tcx>>, from: rustc_middle::thir::ExprKind<'tcx>, state: S as gstate)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[append(
    rustc_middle::thir::ExprKind::Scope {..} => {
        fatal!(gstate, "Scope should have been eliminated at this point");
    },
    rustc_middle::thir::ExprKind::Field {..} => {
        fatal!(gstate, "Field should have been eliminated at this point");
    },
    rustc_middle::thir::ExprKind::NonHirLiteral {..} => {
        fatal!(gstate, "NonHirLiteral should have been eliminated at this point");
    },
)]
pub enum ExprKind {
    Box {
        value: Expr,
    },
    #[disable_mapping]
    MacroInvokation(MacroInvokation),
    If {
        if_then_scope: Scope,
        cond: Expr,
        then: Expr,
        else_opt: Option<Expr>,
    },
    #[map({
        let e = gstate.thir().exprs[*fun].unroll_scope(gstate);
        let fun = match &e.kind {
            /* TODO: see whether [user_ty] below is relevant or not */
            rustc_middle::thir::ExprKind::ZstLiteral {user_ty: _ } => {
                match ty.kind() {
                    /* should we extract substitutions? */
                    rustc_middle::ty::TyKind::FnDef(def, _substs) => {
                        let (hir_id, attributes) = e.hir_id_and_attributes(gstate);
                        let hir_id = hir_id.map(|hir_id| hir_id.index());
                        let contents = Box::new(ExprKind::GlobalName {
                            id: def.sinto(gstate)
                        });
                        Expr {
                            contents,
                            span: e.span.sinto(gstate),
                            ty: e.ty.sinto(gstate),
                            hir_id,
                            attributes,
                        }
                    },
                    ty_kind => {
                        supposely_unreachable!(
                            "CallNotTyFnDef":
                            e, ty_kind
                        );
                        fatal!(gstate, "ZstCallNotTyFnDef")
                    }
                }
            },
            kind => {
                match ty.kind() {
                    rustc_middle::ty::TyKind::FnPtr(..) => {
                        e.sinto(gstate)
                    },
                    ty_kind => {
                        supposely_unreachable!(
                            "CallNotTyFnDef":
                            e, kind, ty_kind
                        );
                        fatal!(gstate, "RefCallNotTyFnPtr")
                    }
                }
            }
        };
        TO_TYPE::Call {
            ty: ty.sinto(gstate),
            args: args.sinto(gstate),
            from_hir_call: from_hir_call.sinto(gstate),
            fn_span: fn_span.sinto(gstate),
            fun,
        }
    })]
    Call {
        ty: Ty,
        fun: Expr, // TODO: can [ty] and [fun.ty] be different?
        args: Vec<Expr>,
        from_hir_call: bool,
        fn_span: Span,
    },
    Deref {
        arg: Expr,
    },
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
    Unary {
        op: UnOp,
        arg: Expr,
    },
    Cast {
        source: Expr,
    },
    Use {
        source: Expr,
    }, // Use a lexpr to get a vexpr.
    NeverToAny {
        source: Expr,
    },
    Pointer {
        cast: PointerCast,
        source: Expr,
    },
    Loop {
        body: Expr,
    },
    Match {
        scrutinee: Expr,
        arms: Vec<Arm>,
    },
    Let {
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
    Block {
        #[serde(flatten)]
        block: Block,
    },
    Assign {
        lhs: Expr,
        rhs: Expr,
    },
    AssignOp {
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
    },
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
    Index {
        lhs: Expr,
        index: Expr,
    },
    VarRef {
        id: LocalIdent,
    },
    #[disable_mapping]
    ConstRef {
        id: ParamConst,
    },
    #[disable_mapping]
    GlobalName {
        id: GlobalIdent,
    },
    UpvarRef {
        closure_def_id: DefId,
        var_hir_id: LocalIdent,
    },
    Borrow {
        borrow_kind: BorrowKind,
        arg: Expr,
    },
    AddressOf {
        mutability: Mutability,
        arg: Expr,
    },
    Break {
        label: Scope,
        value: Option<Expr>,
    },
    Continue {
        label: Scope,
    },
    Return {
        value: Option<Expr>,
    },
    ConstBlock {
        did: DefId,
        substs: Vec<GenericArg>,
    },
    Repeat {
        value: Expr,
        count: Const,
    },
    Array {
        fields: Vec<Expr>,
    },
    Tuple {
        fields: Vec<Expr>,
    },
    Adt(AdtExpr),
    PlaceTypeAscription {
        source: Expr,
        user_ty: Option<CanonicalUserType>,
    },
    ValueTypeAscription {
        source: Expr,
        user_ty: Option<CanonicalUserType>,
    },
    #[custom_arm(FROM_TYPE::Closure(e) => {
        let (thir, expr_entrypoint) = get_thir(e.closure_id, gstate);
        let s = &State {
            thir: thir.clone(),
            owner_id: gstate.owner_id(),
            base: gstate.base(),
            mir: (),
        };
        TO_TYPE::Closure {
            params: thir.params.raw.sinto(s),
            body: expr_entrypoint.sinto(s),
            upvars: e.upvars.sinto(gstate),
            movability: e.movability.sinto(gstate)
        }
    },
    )]
    Closure {
        params: Vec<Param>,
        body: Expr,
        upvars: Vec<Expr>,
        movability: Option<Movability>,
    },
    Literal {
        lit: Spanned<LitKind>,
        neg: bool, // TODO
    },
    //zero space type
    // This is basically used for functions! e.g. `<T>::from`
    ZstLiteral {
        user_ty: Option<CanonicalUserType>,
    },
    NamedConst {
        def_id: GlobalIdent,
        substs: Vec<GenericArg>,
        user_ty: Option<CanonicalUserType>,
    },
    ConstParam {
        param: ParamConst,
        def_id: GlobalIdent,
    },
    StaticRef {
        alloc_id: u64,
        ty: Ty,
        def_id: GlobalIdent,
    },
    Yield {
        value: Expr,
    },
    #[todo]
    Todo(String),
}

pub trait ExprKindExt<'tcx> {
    fn hir_id_and_attributes<S: ExprState<'tcx>>(
        &self,
        s: &S,
    ) -> (Option<rustc_hir::HirId>, Vec<Attribute>);
    fn unroll_scope<S: IsState<'tcx> + HasThir<'tcx>>(
        &self,
        s: &S,
    ) -> rustc_middle::thir::Expr<'tcx>;
}

impl<'tcx> ExprKindExt<'tcx> for rustc_middle::thir::Expr<'tcx> {
    fn hir_id_and_attributes<S: ExprState<'tcx>>(
        &self,
        s: &S,
    ) -> (Option<rustc_hir::HirId>, Vec<Attribute>) {
        match &self.kind {
            rustc_middle::thir::ExprKind::Scope {
                region_scope: scope,
                ..
            } => attribute_from_scope(s, scope),
            _ => (None, vec![]),
        }
    }
    fn unroll_scope<S: IsState<'tcx> + HasThir<'tcx>>(
        &self,
        s: &S,
    ) -> rustc_middle::thir::Expr<'tcx> {
        // TODO: when we see a loop, we should lookup its label! label is actually a scope id
        // we remove scopes here, whence the TODO
        match self.kind {
            rustc_middle::thir::ExprKind::Scope { value, .. } => {
                s.thir().exprs[value].unroll_scope(s)
            }
            _ => self.clone(),
        }
    }
}

impl Expr {
    fn unwrap_borrow(&self) -> Self {
        match &self.contents {
            box ExprKind::Borrow { arg, .. } => arg.clone(),
            _ => self.clone(),
        }
    }
}

/// [FnDef] is a
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct FnDef<Body: IsBody> {
    pub header: FnHeader,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub body: Body,
    pub sig_span: Span,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::FnDecl<'tcx>, state: S as tcx)]
pub struct FnDecl {
    pub inputs: Vec<Ty>,
    pub output: FnRetTy,
    pub c_variadic: bool,
    pub implicit_self: ImplicitSelfKind,
    pub lifetime_elision_allowed: bool,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::FnSig<'tcx>, state: S as tcx)]
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

pub type ThirBody = Expr;

impl<'x, 'tcx, S: BaseState<'tcx> + HasOwnerId> SInto<S, Ty> for rustc_hir::Ty<'x> {
    fn sinto(self: &rustc_hir::Ty<'x>, s: &S) -> Ty {
        let ctx = rustc_hir_analysis::collect::ItemCtxt::new(s.base().tcx, s.owner_id().def_id);
        ctx.to_ty(self).sinto(s)
    }
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::UseKind, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum UseKind {
    Single,
    Glob,
    ListStem,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::IsAuto, state: S as _s)]
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
#[args(<S>, from: rustc_hir::Constness, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Constness {
    Const,
    NotConst,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::Generics<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Generics<Body: IsBody> {
    pub params: Vec<GenericParam<Body>>,
    pub predicates: Vec<WherePredicate<Body>>,
    pub has_where_clause_predicates: bool,
    pub where_clause_span: Span,
    pub span: Span,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::WherePredicate<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum WherePredicate<Body: IsBody> {
    BoundPredicate(WhereBoundPredicate<Body>),
    RegionPredicate(WhereRegionPredicate),
    EqPredicate(WhereEqPredicate),
}

impl<'tcx, S: BaseState<'tcx> + HasOwnerId, Body: IsBody> SInto<S, ImplItem<Body>>
    for rustc_hir::ImplItemRef
{
    fn sinto(&self, s: &S) -> ImplItem<Body> {
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        let impl_item = tcx.hir().impl_item(self.id.clone());
        impl_item.sinto(s)
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ParamName {
    Plain(LocalIdent),
    Fresh,
    Error,
}
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::LifetimeParamKind, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum LifetimeParamKind {
    Explicit,
    Elided,
    Error,
}
#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::AnonConst, state: S as s)]
pub struct AnonConst<Body: IsBody> {
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    #[map({
        body_from_id::<Body, _>(*x, &State {
            thir: (),
            owner_id: hir_id.owner,
            base: s.base(),
            mir: (),
        })
    })]
    pub body: Body,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::GenericParamKind<'tcx>, state: S as tcx)]
pub enum GenericParamKind<Body: IsBody> {
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
        default: Option<AnonConst<Body>>,
    },
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::GenericParam<'tcx>, state: S as s)]
pub struct GenericParam<Body: IsBody> {
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    #[map(match x {
        rustc_hir::ParamName::Plain(loc_ident) =>
            ParamName::Plain(LocalIdent {
                name: loc_ident.as_str().to_string(),
                id: self.hir_id.sinto(s)
            }),
        rustc_hir::ParamName::Fresh =>
            ParamName::Fresh,
        rustc_hir::ParamName::Error =>
            ParamName::Error,
    })]
    pub name: ParamName,
    pub span: Span,
    pub pure_wrt_drop: bool,
    pub kind: GenericParamKind<Body>,
    pub colon_span: Option<Span>,
    #[not_in_source]
    #[map(s.base().tcx.hir().attrs(hir_id.clone()).sinto(s))]
    attributes: Vec<Attribute>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::ImplItem<'tcx>, state: S as s)]
pub struct ImplItem<Body: IsBody> {
    pub ident: Ident,
    pub owner_id: DefId,
    pub generics: Generics<Body>,
    pub kind: ImplItemKind<Body>,
    pub defaultness: Defaultness,
    pub span: Span,
    pub vis_span: Span,
    #[map({
        let tcx = s.base().tcx;
        tcx.hir().attrs(rustc_hir::hir_id::HirId::from(owner_id.clone())).sinto(s)
    })]
    #[not_in_source]
    pub attributes: Vec<Attribute>,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::ImplItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ImplItemKind<Body: IsBody> {
    Const(Ty, Body),
    #[custom_arm(rustc_hir::ImplItemKind::Fn(sig, body) => {
                ImplItemKind::Fn(make_fn_def::<Body, _>(sig, body, tcx))
        },)]
    Fn(FnDef<Body>),
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

impl<
        'tcx,
        S,
        D: Clone,
        T: SInto<S, D> + rustc_middle::ty::TypeFoldable<rustc_middle::ty::TyCtxt<'tcx>>,
    > SInto<S, D> for rustc_middle::ty::subst::EarlyBinder<T>
{
    fn sinto(&self, s: &S) -> D {
        self.clone().subst_identity().sinto(s)
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::Impl<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Impl<Body: IsBody> {
    pub unsafety: Unsafety,
    pub polarity: ImplPolarity,
    pub defaultness: Defaultness,
    pub defaultness_span: Option<Span>,
    pub constness: Constness,
    pub generics: Generics<Body>,
    #[map({
        s.base().tcx.impl_trait_ref(s.owner_id().to_def_id()).sinto(s)
    })]
    pub of_trait: Option<TraitRef>,
    pub self_ty: Ty,
    pub items: Vec<ImplItem<Body>>,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::IsAsync, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum IsAsync {
    Async,
    NotAsync,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::FnRetTy<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum FnRetTy {
    DefaultReturn(Span),
    Return(Ty),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::VariantData<'tcx>, state: S as tcx)]
pub enum VariantData {
    Struct(Vec<HirFieldDef>, bool),
    Tuple(Vec<HirFieldDef>, HirId, GlobalIdent),
    Unit(HirId, GlobalIdent),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::FieldDef<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct HirFieldDef {
    pub span: Span,
    pub vis_span: Span,
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    pub ty: Ty,
    #[not_in_source]
    #[map(s.base().tcx.hir().attrs(hir_id.clone()).sinto(s))]
    attributes: Vec<Attribute>,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::Variant<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Variant<Body: IsBody> {
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: GlobalIdent,
    pub data: VariantData,
    pub disr_expr: Option<AnonConst<Body>>,
    pub span: Span,
    #[not_in_source]
    #[map(s.base().tcx.hir().attrs(hir_id.clone()).sinto(s))]
    attributes: Vec<Attribute>,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::UsePath<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct UsePath {
    pub span: Span,
    #[map(x.iter().map(|res| res.sinto(s)).collect())]
    pub res: Vec<Res>,
    pub segments: Vec<PathSegment>,
    #[not_in_source]
    #[map(self.segments.iter().last().map_or(None, |segment| {
            match s.base().tcx.hir().find_by_def_id(segment.hir_id.owner.def_id) {
                Some(rustc_hir::Node::Item(rustc_hir::Item {
                    ident,
                    kind: rustc_hir::ItemKind::Use(_, _),
                    ..
                })) if ident.name.to_ident_string() != "" => Some(ident.name.to_ident_string()),
                _ => None,
            }
        }))]
    pub rename: Option<String>,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::def::Res, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(PrimTy),
    SelfTyParam {
        trait_: DefId,
    },
    SelfTyAlias {
        alias_to: DefId,
        forbid_generic: bool,
        is_trait_impl: bool,
    },
    SelfCtor(DefId),
    Local(HirId),
    ToolMod,
    NonMacroAttr(NonMacroAttrKind),
    Err,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::PrimTy, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum PrimTy {
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Str,
    Bool,
    Char,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::def::NonMacroAttrKind, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum NonMacroAttrKind {
    Builtin(Symbol),
    Tool,
    DeriveHelper,
    DeriveHelperCompat,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::PathSegment<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct PathSegment {
    pub ident: Ident,
    pub hir_id: HirId,
    pub res: Res,
    #[map(args.map(|args| args.sinto(s)))]
    pub args: Option<HirGenericArgs>,
    pub infer_args: bool,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::ItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ItemKind<Body: IsBody> {
    #[disable_mapping]
    MacroInvokation(MacroInvokation),
    ExternCrate(Option<Symbol>),
    Use(UsePath, UseKind),
    Static(Ty, Mutability, Body),
    Const(Ty, Body),
    #[custom_arm(
            rustc_hir::ItemKind::Fn(sig, generics, body) => {
                ItemKind::Fn(generics.sinto(tcx), make_fn_def::<Body, _>(sig, body, tcx))
            }
        )]
    Fn(Generics<Body>, FnDef<Body>),
    Macro(MacroDef, MacroKind),
    Mod(Vec<Item<Body>>),
    ForeignMod {
        abi: Abi,
        items: Vec<ForeignItem<Body>>,
    },
    GlobalAsm(InlineAsm),
    TyAlias(Ty, Generics<Body>),
    OpaqueTy(OpaqueTy<Body>),
    Enum(EnumDef<Body>, Generics<Body>),
    Struct(VariantData, Generics<Body>),
    Union(VariantData, Generics<Body>),
    Trait(
        IsAuto,
        Unsafety,
        Generics<Body>,
        GenericBounds,
        Vec<TraitItem<Body>>,
    ),
    TraitAlias(Generics<Body>, GenericBounds),
    Impl(Impl<Body>),
}

pub type EnumDef<Body> = Vec<Variant<Body>>;

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::TraitItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum TraitItemKind<Body: IsBody> {
    Const(Ty, Option<Body>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Fn(sig, rustc_hir::TraitFn::Required(id)) => {
            TraitItemKind::RequiredFn(sig.sinto(tcx), id.sinto(tcx))
        }
    )]
    RequiredFn(FnSig, Vec<Ident>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Fn(sig, rustc_hir::TraitFn::Provided(body)) => {
            TraitItemKind::ProvidedFn(make_fn_def::<Body, _>(sig, body, tcx))
        }
    )]
    ProvidedFn(FnDef<Body>),
    #[custom_arm(
        rustc_hir::TraitItemKind::Type(b, ty) => {
            TraitItemKind::Type(b.sinto(tcx), ty.map(|t| t.sinto(tcx)))
        }
    )]
    Type(GenericBounds, Option<Ty>),
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::TraitItem<'tcx>, state: S as s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitItem<Body: IsBody> {
    pub ident: Ident,
    pub owner_id: DefId,
    pub generics: Generics<Body>,
    pub kind: TraitItemKind<Body>,
    pub span: Span,
    pub defaultness: Defaultness,
    #[map({
        let tcx = s.base().tcx;
        tcx.hir().attrs(rustc_hir::hir_id::HirId::from(owner_id.clone())).sinto(s)
    })]
    #[not_in_source]
    pub attributes: Vec<Attribute>,
}

impl<'tcx, S: BaseState<'tcx> + HasOwnerId, Body: IsBody> SInto<S, EnumDef<Body>>
    for rustc_hir::EnumDef<'tcx>
{
    fn sinto(&self, s: &S) -> EnumDef<Body> {
        self.variants.iter().map(|v| v.sinto(s)).collect()
    }
}

impl<'a, S: BaseState<'a> + HasOwnerId, Body: IsBody> SInto<S, TraitItem<Body>>
    for rustc_hir::TraitItemRef
{
    fn sinto(&self, s: &S) -> TraitItem<Body> {
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        tcx.hir().trait_item(self.clone().id).sinto(s)
    }
}

impl<'a, 'tcx, S: BaseState<'tcx>, Body: IsBody> SInto<S, Vec<Item<Body>>> for rustc_hir::Mod<'a> {
    fn sinto(&self, s: &S) -> Vec<Item<Body>> {
        inline_macro_invocations(self.item_ids.iter().copied(), s)
        // .iter()
        // .map(|item_id| item_id.sinto(s))
        // .collect()
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::ForeignItemKind<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ForeignItemKind<Body: IsBody> {
    Fn(FnDecl, Vec<Ident>, Generics<Body>),
    Static(Ty, Mutability),
    Type,
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::ForeignItem<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ForeignItem<Body: IsBody> {
    pub ident: Ident,
    pub kind: ForeignItemKind<Body>,
    pub owner_id: DefId,
    pub span: Span,
    pub vis_span: Span,
}

impl<'a, S: BaseState<'a> + HasOwnerId, Body: IsBody> SInto<S, ForeignItem<Body>>
    for rustc_hir::ForeignItemRef
{
    fn sinto(&self, s: &S) -> ForeignItem<Body> {
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        tcx.hir().foreign_item(self.clone().id).sinto(s)
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::OpaqueTy<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct OpaqueTy<Body: IsBody> {
    pub generics: Generics<Body>,
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

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::TraitRef<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct TraitRef {
    pub def_id: DefId,
    #[from(substs)]
    pub generic_args: Vec<GenericArg>,
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

impl<'tcx, S: BaseState<'tcx> + HasOwnerId> SInto<S, GenericBounds>
    for rustc_hir::GenericBounds<'tcx>
{
    fn sinto(&self, s: &S) -> GenericBounds {
        let tcx = s.base().tcx;

        // According to what kind of node we are looking at, we should
        // either call `predicates_of` or `item_bounds`
        let use_item_bounds = {
            let hir_id = tcx.hir().local_def_id_to_hir_id(s.owner_id().def_id);
            let node = tcx.hir().get(hir_id);
            use rustc_hir as hir;
            matches!(
                node,
                hir::Node::TraitItem(hir::TraitItem {
                    kind: hir::TraitItemKind::Type(..),
                    ..
                }) | hir::Node::Item(hir::Item {
                    kind: hir::ItemKind::OpaqueTy(hir::OpaqueTy { .. }),
                    ..
                })
            )
        };

        let predicates: Vec<_> = if use_item_bounds {
            let list = tcx.item_bounds(s.owner_id().to_def_id()).subst_identity();
            let span = list.default_span(tcx);
            use rustc_middle::query::Key;
            list.into_iter().map(|x| (x, span)).collect()
        } else {
            tcx.predicates_of(s.owner_id().to_def_id())
                .predicates
                .into_iter()
                .cloned()
                .collect()
        };
        predicates
            .iter()
            .map(|(pred, _span)| tcx.erase_late_bound_regions(pred.clone().kind()).sinto(s))
            .collect()
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::OpaqueTyOrigin, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum OpaqueTyOrigin {
    FnReturn(GlobalIdent),
    AsyncFn(GlobalIdent),
    TyAlias { in_assoc_ty: bool },
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
pub struct Item<Body: IsBody> {
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
            base: crate::state::Base {
                opt_def_id: Some(self.owner_id.to_def_id()),
                ..state.base()
            },
            thir: (),
            mir: (),
            owner_id: self.owner_id,
        })
    })]
    pub kind: ItemKind<Body>,
    #[map({
        let tcx = state.base().tcx;
        tcx.hir().attrs(rustc_hir::hir_id::HirId::from(owner_id.clone())).sinto(state)
    })]
    #[not_in_source]
    pub attributes: Vec<Attribute>,
    #[not_in_source]
    #[map(span.macro_backtrace().map(|o| o.sinto(state)).collect())]
    pub expn_backtrace: Vec<ExpnData>,
}

impl<'tcx, S: BaseState<'tcx>, Body: IsBody> SInto<S, Item<Body>> for rustc_hir::ItemId {
    fn sinto(&self, s: &S) -> Item<Body> {
        let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
        tcx.hir().item(self.clone()).sinto(s)
    }
}

pub type Ident = (Symbol, Span);

impl<'tcx, S: BaseState<'tcx>> SInto<S, Ident> for rustc_span::symbol::Ident {
    fn sinto(&self, s: &S) -> Ident {
        (self.name.sinto(s), self.span.sinto(s))
    }
}

#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx> + HasOwnerId>, from: rustc_hir::WhereBoundPredicate<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct WhereBoundPredicate<Body: IsBody> {
    pub hir_id: HirId,
    pub span: Span,
    pub origin: PredicateOrigin,
    pub bound_generic_params: Vec<GenericParam<Body>>,
    pub bounded_ty: Ty,
    pub bounds: GenericBounds,
}

#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::PredicateOrigin, state: S as _s)]
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum PredicateOrigin {
    WhereClause,
    GenericParam,
    ImplTrait,
}
