//! Copies of the relevant type-level types. These are semantically-rich representations of
//! type-level concepts such as types and trait references.
use crate::prelude::*;
use crate::sinto_as_usize;
use crate::sinto_todo;
use std::sync::Arc;

#[cfg(feature = "rustc")]
use rustc_middle::ty;

/// Generic container for decorating items with a type, a span,
/// attributes and other meta-data.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Decorated<T> {
    pub ty: Ty,
    pub span: Span,
    pub contents: Box<T>,
    pub hir_id: Option<(usize, usize)>,
    pub attributes: Vec<Attribute>,
}

/// Reflects [`rustc_middle::infer::canonical::CanonicalTyVarKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalTyVarKind, state: S as gstate)]
pub enum CanonicalTyVarKind {
    General(UniverseIndex),
    Int,
    Float,
}

sinto_as_usize!(rustc_middle::ty, UniverseIndex);

/// Reflects [`rustc_middle::ty::ParamTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ParamTy, state: S as gstate)]
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`rustc_middle::ty::ParamConst`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: rustc_middle::ty::ParamConst, state: S as gstate)]
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

/// A predicate without `Self`, for use in `dyn Trait`.
///
/// Reflects [`rustc_middle::ty::ExistentialPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ExistentialPredicate<'tcx>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExistentialPredicate {
    /// E.g. `From<u64>`. Note that this isn't `T: From<u64>` with a given `T`, this is just
    /// `From<u64>`. Could be written `?: From<u64>`.
    Trait(ExistentialTraitRef),
    /// E.g. `Iterator::Item = u64`. Could be written `<? as Iterator>::Item = u64`.
    Projection(ExistentialProjection),
    /// E.g. `Send`.
    AutoTrait(DefId),
}

/// Reflects [`rustc_type_ir::ExistentialTraitRef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_type_ir::ExistentialTraitRef<ty::TyCtxt<'tcx>>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExistentialTraitRef {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
}

/// Reflects [`rustc_type_ir::ExistentialProjection`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_type_ir::ExistentialProjection<ty::TyCtxt<'tcx>>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExistentialProjection {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
    pub term: Term,
}

/// Reflects [`rustc_middle::ty::DynKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: rustc_middle::ty::DynKind, state: S as _s)]
pub enum DynKind {
    Dyn,
    DynStar,
}

/// Reflects [`rustc_middle::ty::BoundTyKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundTyKind, state: S as gstate)]
pub enum BoundTyKind {
    Anon,
    Param(DefId, Symbol),
}

/// Reflects [`rustc_middle::ty::BoundTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundTy, state: S as gstate)]
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

sinto_as_usize!(rustc_middle::ty, BoundVar);

/// Reflects [`rustc_middle::ty::BoundRegionKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundRegionKind, state: S as gstate)]
pub enum BoundRegionKind {
    BrAnon,
    BrNamed(DefId, Symbol),
    BrEnv,
}

/// Reflects [`rustc_middle::ty::BoundRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundRegion, state: S as gstate)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

/// Reflects [`rustc_middle::ty::PlaceholderRegion`]
pub type PlaceholderRegion = Placeholder<BoundRegion>;
/// Reflects [`rustc_middle::ty::PlaceholderConst`]
pub type PlaceholderConst = Placeholder<BoundVar>;
/// Reflects [`rustc_middle::ty::PlaceholderType`]
pub type PlaceholderType = Placeholder<BoundTy>;

/// Reflects [`rustc_middle::ty::Placeholder`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Placeholder<T> {
    pub universe: UniverseIndex,
    pub bound: T,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Placeholder<U>>
    for rustc_middle::ty::Placeholder<T>
{
    fn sinto(&self, s: &S) -> Placeholder<U> {
        Placeholder {
            universe: self.universe.sinto(s),
            bound: self.bound.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::infer::canonical::Canonical`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct Canonical<T> {
    pub max_universe: UniverseIndex,
    pub variables: Vec<CanonicalVarInfo>,
    pub value: T,
}
/// Reflects [`rustc_middle::ty::CanonicalUserType`]
pub type CanonicalUserType = Canonical<UserType>;

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Canonical<U>>
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

/// Reflects [`rustc_middle::infer::canonical::CanonicalVarKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::infer::canonical::CanonicalVarKind<ty::TyCtxt<'tcx>>, state: S as gstate)]
pub enum CanonicalVarInfo {
    Ty(CanonicalTyVarKind),
    PlaceholderTy(PlaceholderType),
    Region(UniverseIndex),
    PlaceholderRegion(PlaceholderRegion),
    Const(UniverseIndex),
    PlaceholderConst(PlaceholderConst),
    Effect,
}

/// Reflects [`rustc_middle::ty::UserSelfTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::UserSelfTy<'tcx>, state: S as gstate)]
pub struct UserSelfTy {
    pub impl_def_id: DefId,
    pub self_ty: Ty,
}

/// Reflects [`rustc_middle::ty::UserArgs`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::UserArgs<'tcx>, state: S as gstate)]
pub struct UserArgs {
    pub args: Vec<GenericArg>,
    pub user_self_ty: Option<UserSelfTy>,
}

/// Reflects [`rustc_middle::ty::UserType`]: this is currently
/// disabled, and everything is printed as debug in the
/// [`UserType::Todo`] variant.
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::UserType<'tcx>, state: S as _s)]
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
    // See: https://github.com/hacspec/hax/pull/209

    // Ty(Ty),
    // TypeOf(DefId, UserArgs),
    #[todo]
    Todo(String),
}

/// Reflects [`rustc_middle::ty::VariantDiscr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::VariantDiscr, state: S as gstate)]
pub enum DiscriminantDefinition {
    Explicit(DefId),
    Relative(u32),
}

/// Reflects [`rustc_middle::ty::util::Discr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::util::Discr<'tcx>, state: S as gstate)]
pub struct DiscriminantValue {
    pub val: u128,
    pub ty: Ty,
}

/// Reflects [`rustc_middle::ty::Visibility`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Visibility<Id> {
    Public,
    Restricted(Id),
}

#[cfg(feature = "rustc")]
impl<S, T: SInto<S, U>, U> SInto<S, Visibility<U>> for rustc_middle::ty::Visibility<T> {
    fn sinto(&self, s: &S) -> Visibility<U> {
        use rustc_middle::ty::Visibility as T;
        match self {
            T::Public => Visibility::Public,
            T::Restricted(id) => Visibility::Restricted(id.sinto(s)),
        }
    }
}

/// Reflects [`rustc_middle::ty::FieldDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct FieldDef {
    pub did: DefId,
    /// Field definition of [tuple
    /// structs](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-tuple-structs-without-named-fields-to-create-different-types)
    /// are anonymous, in that case `name` is [`None`].
    pub name: Option<Symbol>,
    pub vis: Visibility<DefId>,
    pub ty: Ty,
    pub span: Span,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, FieldDef> for rustc_middle::ty::FieldDef {
    fn sinto(&self, s: &S) -> FieldDef {
        let tcx = s.base().tcx;
        let ty = {
            let generics = rustc_middle::ty::GenericArgs::identity_for_item(tcx, self.did);
            self.ty(tcx, generics).sinto(s)
        };
        let name = {
            let name = self.name.sinto(s);
            let is_user_provided = {
                // SH: Note that the only way I found of checking if the user wrote the name or if it
                // is just an integer generated by rustc is by checking if it is just made of
                // numerals...
                name.parse::<usize>().is_err()
            };
            is_user_provided.then_some(name)
        };

        FieldDef {
            did: self.did.sinto(s),
            name,
            vis: self.vis.sinto(s),
            ty,
            span: tcx.def_span(self.did).sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::VariantDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct VariantDef {
    pub def_id: DefId,
    pub ctor: Option<(CtorKind, DefId)>,
    pub name: Symbol,
    pub discr_def: DiscriminantDefinition,
    pub discr_val: DiscriminantValue,
    /// The definitions of the fields on this variant. In case of
    /// [tuple
    /// structs](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-tuple-structs-without-named-fields-to-create-different-types),
    /// the fields are anonymous, otherwise fields are named.
    pub fields: Vec<FieldDef>,
    /// Span of the definition of the variant
    pub span: Span,
}

#[cfg(feature = "rustc")]
impl VariantDef {
    fn sfrom<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        def: &ty::VariantDef,
        discr_val: ty::util::Discr<'tcx>,
    ) -> Self {
        VariantDef {
            def_id: def.def_id.sinto(s),
            ctor: def.ctor.sinto(s),
            name: def.name.sinto(s),
            discr_def: def.discr.sinto(s),
            discr_val: discr_val.sinto(s),
            fields: def.fields.raw.sinto(s),
            span: s.base().tcx.def_span(def.def_id).sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::EarlyParamRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::EarlyParamRegion, state: S as gstate)]
pub struct EarlyParamRegion {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`rustc_middle::ty::LateParamRegion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::LateParamRegion, state: S as gstate)]
pub struct LateParamRegion {
    pub scope: DefId,
    pub bound_region: BoundRegionKind,
}

/// Reflects [`rustc_middle::ty::RegionKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::RegionKind<'tcx>, state: S as gstate)]
pub enum RegionKind {
    ReEarlyParam(EarlyParamRegion),
    ReBound(DebruijnIndex, BoundRegion),
    ReLateParam(LateParamRegion),
    ReStatic,
    ReVar(RegionVid),
    RePlaceholder(PlaceholderRegion),
    ReErased,
    ReError(ErrorGuaranteed),
}

sinto_as_usize!(rustc_middle::ty, DebruijnIndex);
sinto_as_usize!(rustc_middle::ty, RegionVid);

/// Reflects [`rustc_middle::ty::Region`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::Region<'tcx>, state: S as s)]
pub struct Region {
    #[value(self.kind().sinto(s))]
    pub kind: RegionKind,
}

/// Reflects both [`rustc_middle::ty::GenericArg`] and [`rustc_middle::ty::GenericArgKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::GenericArgKind<'tcx>, state: S as s)]
pub enum GenericArg {
    Lifetime(Region),
    Type(Ty),
    Const(ConstantExpr),
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GenericArg> for rustc_middle::ty::GenericArg<'tcx> {
    fn sinto(&self, s: &S) -> GenericArg {
        self.unpack().sinto(s)
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Vec<GenericArg>>
    for rustc_middle::ty::GenericArgsRef<'tcx>
{
    fn sinto(&self, s: &S) -> Vec<GenericArg> {
        self.iter().map(|v| v.unpack().sinto(s)).collect()
    }
}

/// Reflects both [`rustc_middle::ty::GenericArg`] and [`rustc_middle::ty::GenericArgKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::LitIntType, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum LitIntType {
    Signed(IntTy),
    Unsigned(UintTy),
    Unsuffixed,
}

/// Reflects partially [`rustc_middle::ty::InferTy`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
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

/// Reflects [`rustc_type_ir::IntTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::IntTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

/// Reflects [`rustc_type_ir::FloatTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::FloatTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[cfg(feature = "rustc")]
impl<'tcx, S> SInto<S, FloatTy> for rustc_ast::ast::FloatTy {
    fn sinto(&self, _: &S) -> FloatTy {
        use rustc_ast::ast::FloatTy as T;
        match self {
            T::F16 => FloatTy::F16,
            T::F32 => FloatTy::F32,
            T::F64 => FloatTy::F64,
            T::F128 => FloatTy::F128,
        }
    }
}

#[cfg(feature = "rustc")]
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
#[cfg(feature = "rustc")]
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

/// Reflects [`rustc_type_ir::UintTy`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_type_ir::UintTy, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Copy, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl ToString for IntTy {
    fn to_string(&self) -> String {
        use IntTy::*;
        match self {
            Isize => "isize".to_string(),
            I8 => "i8".to_string(),
            I16 => "i16".to_string(),
            I32 => "i32".to_string(),
            I64 => "i64".to_string(),
            I128 => "i128".to_string(),
        }
    }
}

impl ToString for UintTy {
    fn to_string(&self) -> String {
        use UintTy::*;
        match self {
            Usize => "usize".to_string(),
            U8 => "u8".to_string(),
            U16 => "u16".to_string(),
            U32 => "u32".to_string(),
            U64 => "u64".to_string(),
            U128 => "u128".to_string(),
        }
    }
}

/// Reflects [`rustc_middle::ty::TypeAndMut`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TypeAndMut<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeAndMut {
    pub ty: Box<Ty>,
    pub mutbl: Mutability,
}

#[cfg(feature = "rustc")]
impl<S, U, T: SInto<S, U>> SInto<S, Vec<U>> for rustc_middle::ty::List<T> {
    fn sinto(&self, s: &S) -> Vec<U> {
        self.iter().map(|x| x.sinto(s)).collect()
    }
}

/// Reflects [`rustc_middle::ty::GenericParamDef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::GenericParamDef, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct GenericParamDef {
    pub name: Symbol,
    pub def_id: DefId,
    pub index: u32,
    pub pure_wrt_drop: bool,
    #[value(
        match self.kind {
            ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
            ty::GenericParamDefKind::Type { has_default, synthetic } => GenericParamDefKind::Type { has_default, synthetic },
            ty::GenericParamDefKind::Const { has_default, is_host_effect, .. } => {
                let ty = s.base().tcx.type_of(self.def_id).instantiate_identity().sinto(s);
                GenericParamDefKind::Const { has_default, is_host_effect, ty }
            },
        }
    )]
    pub kind: GenericParamDefKind,
}

/// Reflects [`rustc_middle::ty::GenericParamDefKind`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum GenericParamDefKind {
    Lifetime,
    Type {
        has_default: bool,
        synthetic: bool,
    },
    Const {
        has_default: bool,
        is_host_effect: bool,
        ty: Ty,
    },
}

/// Reflects [`rustc_middle::ty::Generics`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::Generics, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct TyGenerics {
    pub parent: Option<DefId>,
    pub parent_count: usize,
    #[from(own_params)]
    pub params: Vec<GenericParamDef>,
    // pub param_def_id_to_index: FxHashMap<DefId, u32>,
    pub has_self: bool,
    pub has_late_bound_regions: Option<Span>,
}

/// This type merges the information from
/// `rustc_type_ir::AliasKind` and `rustc_middle::ty::AliasTy`
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Alias {
    pub kind: AliasKind,
    pub args: Vec<GenericArg>,
    pub def_id: DefId,
}

/// Reflects [`rustc_middle::ty::AliasKind`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AliasKind {
    /// The projection of a trait type: `<Ty as Trait<...>>::Type<...>`
    Projection {
        /// The `impl Trait for Ty` in `Ty: Trait<..., Type = U>`.
        impl_expr: ImplExpr,
        /// The `Type` in `Ty: Trait<..., Type = U>`.
        assoc_item: AssocItem,
    },
    /// An associated type in an inherent impl.
    Inherent,
    /// An `impl Trait` opaque type.
    Opaque {
        /// The real type hidden inside this opaque type.
        hidden_ty: Ty,
    },
    /// A type alias that references opaque types. Likely to always be normalized away.
    Weak,
}

#[cfg(feature = "rustc")]
impl Alias {
    #[tracing::instrument(level = "trace", skip(s))]
    fn from<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        alias_kind: &rustc_type_ir::AliasTyKind,
        alias_ty: &rustc_middle::ty::AliasTy<'tcx>,
    ) -> TyKind {
        let tcx = s.base().tcx;
        use rustc_type_ir::AliasTyKind as RustAliasKind;
        let kind = match alias_kind {
            RustAliasKind::Projection => {
                let trait_ref = alias_ty.trait_ref(tcx);
                // In a case like:
                // ```
                // impl<T, U> Trait for Result<T, U>
                // where
                //     for<'a> &'a Result<T, U>: IntoIterator,
                //     for<'a> <&'a Result<T, U> as IntoIterator>::Item: Copy,
                // {}
                // ```
                // the `&'a Result<T, U> as IntoIterator` trait ref has escaping bound variables
                // yet we dont have a binder around (could even be several). Binding this correctly
                // is therefore difficult. Since our trait resolution ignores lifetimes anyway, we
                // just erase them. See also https://github.com/hacspec/hax/issues/747.
                let trait_ref = crate::traits::erase_and_norm(tcx, s.param_env(), trait_ref);
                AliasKind::Projection {
                    assoc_item: tcx.associated_item(alias_ty.def_id).sinto(s),
                    impl_expr: solve_trait(s, ty::Binder::dummy(trait_ref)),
                }
            }
            RustAliasKind::Inherent => AliasKind::Inherent,
            RustAliasKind::Opaque => {
                // Reveal the underlying `impl Trait` type.
                let ty = tcx.type_of(alias_ty.def_id).instantiate(tcx, alias_ty.args);
                AliasKind::Opaque {
                    hidden_ty: ty.sinto(s),
                }
            }
            RustAliasKind::Weak => AliasKind::Weak,
        };
        TyKind::Alias(Alias {
            kind,
            args: alias_ty.args.sinto(s),
            def_id: alias_ty.def_id.sinto(s),
        })
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Box<Ty>> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Box<Ty> {
        Box::new(self.sinto(s))
    }
}

/// Reflects [`rustc_middle::ty::Ty`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ty {
    pub kind: Arc<TyKind>,
}

impl Ty {
    pub fn kind(&self) -> &TyKind {
        self.kind.as_ref()
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Ty> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Ty {
        if let Some(ty) = s.with_cache(|cache| cache.tys.get(self).cloned()) {
            return ty;
        }
        let ty = Ty {
            kind: Arc::new(self.kind().sinto(s)),
        };
        s.with_cache(|cache| cache.tys.insert(*self, ty.clone()));
        ty
    }
}

/// Reflects [`rustc_middle::ty::TyKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TyKind<'tcx>, state: S as state)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyKind {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),

    #[custom_arm(
        rustc_middle::ty::TyKind::FnPtr(sig) => arrow_of_sig(sig, state),
        rustc_middle::ty::TyKind::FnDef(def, generics) => {
            let tcx = state.base().tcx;
            arrow_of_sig(&tcx.fn_sig(*def).instantiate(tcx, generics), state)
        },
        FROM_TYPE::Closure (_defid, generics) => {
            let sig = generics.as_closure().sig();
            let sig = state.base().tcx.signature_unclosure(sig, rustc_hir::Safety::Safe);
            arrow_of_sig(&sig, state)
        },
    )]
    /// Reflects [`rustc_middle::ty::TyKind::FnPtr`], [`rustc_middle::ty::TyKind::FnDef`] and [`rustc_middle::ty::TyKind::Closure`]
    Arrow(Box<PolyFnSig>),

    #[custom_arm(
        rustc_middle::ty::TyKind::Adt(adt_def, generics) => {
            let def_id = adt_def.did().sinto(state);
            let generic_args: Vec<GenericArg> = generics.sinto(state);
            let trait_refs = solve_item_traits(state, adt_def.did(), generics, None);
            TyKind::Adt { def_id, generic_args, trait_refs }
        },
    )]
    Adt {
        /// Reflects [`rustc_middle::ty::TyKind::Adt`]'s substitutions
        generic_args: Vec<GenericArg>,
        /// Predicates required by the type, e.g. `T: Sized` for `Option<T>` or `B: 'a + ToOwned`
        /// for `Cow<'a, B>`.
        trait_refs: Vec<ImplExpr>,
        def_id: DefId,
    },
    Foreign(DefId),
    Str,
    Array(Box<Ty>, #[map(Box::new(x.sinto(state)))] Box<ConstantExpr>),
    Slice(Box<Ty>),
    RawPtr(Box<Ty>, Mutability),
    Ref(Region, Box<Ty>, Mutability),
    Dynamic(Vec<Binder<ExistentialPredicate>>, Region, DynKind),
    Coroutine(DefId, Vec<GenericArg>),
    Never,
    Tuple(Vec<Ty>),
    #[custom_arm(
        rustc_middle::ty::TyKind::Alias(alias_kind, alias_ty) => {
            Alias::from(state, alias_kind, alias_ty)
        },
    )]
    Alias(Alias),
    Param(ParamTy),
    Bound(DebruijnIndex, BoundTy),
    Placeholder(PlaceholderType),
    Infer(InferTy),
    #[custom_arm(rustc_middle::ty::TyKind::Error(..) => TyKind::Error,)]
    Error,
    #[todo]
    Todo(String),
}

/// Reflects [`rustc_middle::ty::Variance`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::Variance, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum Variance {
    Covariant,
    Invariant,
    Contravariant,
    Bivariant,
}

/// Reflects [`rustc_middle::ty::CanonicalUserTypeAnnotation`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::CanonicalUserTypeAnnotation<'tcx>, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct CanonicalUserTypeAnnotation {
    pub user_ty: CanonicalUserType,
    pub span: Span,
    pub inferred_ty: Ty,
}

/// Reflects [`rustc_middle::ty::AdtKind`]
#[derive_group(Serializers)]
#[derive(AdtInto, Copy, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::AdtKind, state: S as _s)]
pub enum AdtKind {
    Struct,
    Union,
    Enum,
}

// This comes from MIR
// TODO: add the generics and the predicates
/// Reflects [`rustc_middle::ty::AdtDef`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub struct AdtDef {
    pub did: DefId,
    pub adt_kind: AdtKind,
    pub variants: IndexVec<VariantIdx, VariantDef>,
    pub flags: AdtFlags,
    pub repr: ReprOptions,
}

sinto_todo!(rustc_middle::ty, AdtFlags);

/// Reflects [`rustc_middle::ty::ReprOptions`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ReprOptions, state: S as s)]
pub struct ReprOptions {
    pub int: Option<IntegerType>,
    #[value({
        use crate::rustc_middle::ty::util::IntTypeExt;
        self.discr_type().to_ty(s.base().tcx).sinto(s)
    })]
    pub typ: Ty,
    pub align: Option<Align>,
    pub pack: Option<Align>,
    pub flags: ReprFlags,
    pub field_shuffle_seed: u64,
}

sinto_todo!(rustc_abi, IntegerType);
sinto_todo!(rustc_abi, ReprFlags);
sinto_todo!(rustc_abi, Align);

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, AdtDef> for rustc_middle::ty::AdtDef<'tcx> {
    fn sinto(&self, s: &S) -> AdtDef {
        let variants = self
            .variants()
            .iter_enumerated()
            .map(|(variant_idx, variant)| {
                let discr = if self.is_enum() {
                    self.discriminant_for_variant(s.base().tcx, variant_idx)
                } else {
                    // Structs and unions have a single variant.
                    assert_eq!(variant_idx.index(), 0);
                    rustc_middle::ty::util::Discr {
                        val: 0,
                        ty: s.base().tcx.types.isize,
                    }
                };
                VariantDef::sfrom(s, variant, discr)
            })
            .collect();
        AdtDef {
            did: self.did().sinto(s),
            adt_kind: self.adt_kind().sinto(s),
            variants,
            flags: self.flags().sinto(s),
            repr: self.repr().sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::adjustment::PointerCoercion`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::adjustment::PointerCoercion, state: S as gstate)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema)]
pub enum PointerCoercion {
    ReifyFnPointer,
    UnsafeFnPointer,
    ClosureFnPointer(Safety),
    MutToConstPointer,
    ArrayToPointer,
    Unsize,
}

sinto_todo!(rustc_middle::ty, ScalarInt);

/// Reflects [`rustc_middle::ty::FnSig`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::FnSig<'tcx>, state: S as s)]
pub struct TyFnSig {
    #[value(self.inputs().sinto(s))]
    pub inputs: Vec<Ty>,
    #[value(self.output().sinto(s))]
    pub output: Ty,
    pub c_variadic: bool,
    pub safety: Safety,
    pub abi: Abi,
}

/// Reflects [`rustc_middle::ty::PolyFnSig`]
pub type PolyFnSig = Binder<TyFnSig>;

/// Reflects [`rustc_middle::ty::TraitRef`]
#[derive_group(Serializers)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TraitRef<'tcx>, state: S as tcx)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitRef {
    pub def_id: DefId,
    #[from(args)]
    /// reflects the `args` field
    pub generic_args: Vec<GenericArg>,
}

/// Reflects [`rustc_middle::ty::TraitPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::TraitPredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
    #[map(*x == rustc_middle::ty::PredicatePolarity::Positive)]
    #[from(polarity)]
    pub is_positive: bool,
}

/// Reflects [`rustc_middle::ty::OutlivesPredicate`] as a named struct
/// instead of a tuple struct. This is because the script converting
/// JSONSchema types to OCaml doesn't support tuple structs, and this
/// is the only tuple struct in the whole AST.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct OutlivesPredicate<T> {
    pub lhs: T,
    pub rhs: Region,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T, U> SInto<S, OutlivesPredicate<U>>
    for rustc_middle::ty::OutlivesPredicate<'tcx, T>
where
    T: SInto<S, U>,
{
    fn sinto(&self, s: &S) -> OutlivesPredicate<U> where {
        OutlivesPredicate {
            lhs: self.0.sinto(s),
            rhs: self.1.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::ty::RegionOutlivesPredicate`]
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;
/// Reflects [`rustc_middle::ty::TypeOutlivesPredicate`]
pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;

/// Reflects [`rustc_middle::ty::Term`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Ty(Ty),
    Const(ConstantExpr),
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Term> for rustc_middle::ty::Term<'tcx> {
    fn sinto(&self, s: &S) -> Term {
        use rustc_middle::ty::TermKind;
        match self.unpack() {
            TermKind::Ty(ty) => Term::Ty(ty.sinto(s)),
            TermKind::Const(c) => Term::Const(c.sinto(s)),
        }
    }
}

/// Expresses a constraints over an associated type.
///
/// For instance:
/// ```text
/// fn f<T : Foo<S = String>>(...)
///              ^^^^^^^^^^
/// ```
/// (provided the trait `Foo` has an associated type `S`).
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProjectionPredicate {
    /// The `impl Trait for Ty` in `Ty: Trait<..., Type = U>`.
    pub impl_expr: ImplExpr,
    /// The `Type` in `Ty: Trait<..., Type = U>`.
    pub assoc_item: AssocItem,
    /// The type `U` in `Ty: Trait<..., Type = U>`.
    pub ty: Ty,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderBinderState<'tcx>> SInto<S, ProjectionPredicate>
    for rustc_middle::ty::ProjectionPredicate<'tcx>
{
    fn sinto(&self, s: &S) -> ProjectionPredicate {
        let tcx = s.base().tcx;
        let alias_ty = &self.projection_term.expect_ty(tcx);
        let poly_trait_ref = s.binder().rebind(alias_ty.trait_ref(tcx));
        let Term::Ty(ty) = self.term.sinto(s) else {
            unreachable!()
        };
        ProjectionPredicate {
            impl_expr: solve_trait(s, poly_trait_ref),
            assoc_item: tcx.associated_item(alias_ty.def_id).sinto(s),
            ty,
        }
    }
}

/// Reflects [`rustc_middle::ty::ClauseKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderBinderState<'tcx>>, from: rustc_middle::ty::ClauseKind<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClauseKind {
    Trait(TraitPredicate),
    RegionOutlives(RegionOutlivesPredicate),
    TypeOutlives(TypeOutlivesPredicate),
    Projection(ProjectionPredicate),
    ConstArgHasType(ConstantExpr, Ty),
    WellFormed(GenericArg),
    ConstEvaluatable(ConstantExpr),
}

/// Reflects [`rustc_middle::ty::Clause`] and adds a hash-consed predicate identifier.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Clause {
    pub kind: Binder<ClauseKind>,
    pub id: PredicateId,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Clause> for rustc_middle::ty::Clause<'tcx> {
    fn sinto(&self, s: &S) -> Clause {
        let kind = self.kind().sinto(s);
        let id = kind.clone().map(PredicateKind::Clause).predicate_id();
        Clause { kind, id }
    }
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Clause>
    for rustc_middle::ty::PolyTraitPredicate<'tcx>
{
    fn sinto(&self, s: &S) -> Clause {
        let kind: Binder<_> = self.sinto(s);
        let kind: Binder<ClauseKind> = kind.map(ClauseKind::Trait);
        let id = kind.clone().map(PredicateKind::Clause).predicate_id();
        Clause { kind, id }
    }
}

/// Reflects [`rustc_middle::ty::Predicate`] and adds a hash-consed predicate identifier.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Predicate {
    pub kind: Binder<PredicateKind>,
    pub id: PredicateId,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Predicate> for rustc_middle::ty::Predicate<'tcx> {
    fn sinto(&self, s: &S) -> Predicate {
        let kind = self.kind().sinto(s);
        let id = kind.predicate_id();
        Predicate { kind, id }
    }
}

/// Reflects [`rustc_middle::ty::BoundVariableKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::BoundVariableKind, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum BoundVariableKind {
    Ty(BoundTyKind),
    Region(BoundRegionKind),
    Const,
}

/// Reflects [`rustc_middle::ty::Binder`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Binder<T> {
    pub value: T,
    pub bound_vars: Vec<BoundVariableKind>,
}

impl<T> Binder<T> {
    pub fn as_ref(&self) -> Binder<&T> {
        Binder {
            value: &self.value,
            bound_vars: self.bound_vars.clone(),
        }
    }

    pub fn hax_skip_binder(self) -> T {
        self.value
    }

    pub fn hax_skip_binder_ref(&self) -> &T {
        &self.value
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Binder<U> {
        Binder {
            value: f(self.value),
            bound_vars: self.bound_vars,
        }
    }

    pub fn inner_mut(&mut self) -> &mut T {
        &mut self.value
    }

    pub fn rebind<U>(&self, value: U) -> Binder<U> {
        self.as_ref().map(|_| value)
    }
}

/// Reflects [`rustc_middle::ty::GenericPredicates`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::GenericPredicates<'tcx>, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    // FIXME: Switch from `Predicate` to `Clause` (will require correct handling of binders).
    #[value(self.predicates.iter().map(|(clause, span)| (clause.as_predicate().sinto(s), span.sinto(s))).collect())]
    pub predicates: Vec<(Predicate, Span)>,
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>, T1, T2> SInto<S, Binder<T2>>
    for rustc_middle::ty::Binder<'tcx, T1>
where
    T1: SInto<StateWithBinder<'tcx>, T2>,
{
    fn sinto(&self, s: &S) -> Binder<T2> {
        let bound_vars = self.bound_vars().sinto(s);
        let value = {
            let under_binder_s = &State {
                base: s.base(),
                owner_id: s.owner_id(),
                binder: self.as_ref().map_bound(|_| ()),
                thir: (),
                mir: (),
            };
            self.as_ref().skip_binder().sinto(under_binder_s)
        };
        Binder { value, bound_vars }
    }
}

/// Reflects [`rustc_middle::ty::SubtypePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::SubtypePredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubtypePredicate {
    pub a_is_expected: bool,
    pub a: Ty,
    pub b: Ty,
}

/// Reflects [`rustc_middle::ty::CoercePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::CoercePredicate<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct CoercePredicate {
    pub a: Ty,
    pub b: Ty,
}

/// Reflects [`rustc_middle::ty::AliasRelationDirection`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::AliasRelationDirection, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AliasRelationDirection {
    Equate,
    Subtype,
}

/// Reflects [`rustc_middle::ty::ClosureArgs`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: ty::ClosureArgs<ty::TyCtxt<'tcx>>, state: S as s)]
#[derive(Clone, Debug, JsonSchema)]
#[derive_group(Serializers)]
pub struct ClosureArgs {
    #[value(self.kind().sinto(s))]
    pub kind: ClosureKind,
    #[value(self.parent_args().sinto(s))]
    pub parent_args: Vec<GenericArg>,
    #[value(self.sig().sinto(s))]
    pub sig: PolyFnSig,
    #[value(self.upvar_tys().sinto(s))]
    pub upvar_tys: Vec<Ty>,
}

/// Reflects [`rustc_middle::ty::ClosureKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_middle::ty::ClosureKind, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

sinto_todo!(rustc_middle::ty, NormalizesTo<'tcx>);

/// Reflects [`rustc_middle::ty::PredicateKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderBinderState<'tcx>>, from: rustc_middle::ty::PredicateKind<'tcx>, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum PredicateKind {
    Clause(ClauseKind),
    ObjectSafe(DefId),
    Subtype(SubtypePredicate),
    Coerce(CoercePredicate),
    ConstEquate(ConstantExpr, ConstantExpr),
    Ambiguous,
    AliasRelate(Term, Term, AliasRelationDirection),
    NormalizesTo(NormalizesTo),
}

/// Reflects [`rustc_middle::ty::ImplSubject`]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImplSubject {
    Trait {
        /// The trait that is implemented by this impl block.
        trait_pred: TraitPredicate,
        /// The `ImplExpr`s required to satisfy the predicates on the trait declaration. E.g.:
        /// ```ignore
        /// trait Foo: Bar {}
        /// impl Foo for () {} // would supply an `ImplExpr` for `Self: Bar`.
        /// ```
        required_impl_exprs: Vec<ImplExpr>,
    },
    Inherent(Ty),
}

#[cfg(feature = "rustc")]
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ImplSubject> for ty::ImplSubject<'tcx> {
    fn sinto(&self, s: &S) -> ImplSubject {
        let tcx = s.base().tcx;
        match self {
            ty::ImplSubject::Inherent(ty) => ImplSubject::Inherent(ty.sinto(s)),
            ty::ImplSubject::Trait(trait_ref) => {
                // Also record the polarity.
                let polarity = tcx.impl_polarity(s.owner_id());
                let trait_pred = TraitPredicate {
                    trait_ref: trait_ref.sinto(s),
                    is_positive: matches!(polarity, rustc_middle::ty::ImplPolarity::Positive),
                };
                let required_impl_exprs =
                    solve_item_traits(s, trait_ref.def_id, trait_ref.args, None);
                ImplSubject::Trait {
                    trait_pred,
                    required_impl_exprs,
                }
            }
        }
    }
}

#[cfg(feature = "rustc")]
fn get_container_for_assoc_item<'tcx, S: BaseState<'tcx>>(
    s: &S,
    item: &ty::AssocItem,
) -> AssocItemContainer {
    let container_id = item.container_id(s.base().tcx);
    match item.container {
        ty::AssocItemContainer::TraitContainer => AssocItemContainer::TraitContainer {
            trait_id: container_id.sinto(s),
        },
        ty::AssocItemContainer::ImplContainer => {
            if let Some(implemented_trait_item) = item.trait_item_def_id {
                AssocItemContainer::TraitImplContainer {
                    impl_id: container_id.sinto(s),
                    implemented_trait: s
                        .base()
                        .tcx
                        .trait_of_item(implemented_trait_item)
                        .unwrap()
                        .sinto(s),
                    implemented_trait_item: implemented_trait_item.sinto(s),
                    overrides_default: s.base().tcx.defaultness(implemented_trait_item).has_value(),
                }
            } else {
                AssocItemContainer::InherentImplContainer {
                    impl_id: container_id.sinto(s),
                }
            }
        }
    }
}

/// Reflects [`rustc_middle::ty::AssocItem`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::AssocItem, state: S as s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct AssocItem {
    pub def_id: DefId,
    pub name: Symbol,
    pub kind: AssocKind,
    #[value(get_container_for_assoc_item(s, self))]
    pub container: AssocItemContainer,
    /// Whether this item has a value (e.g. this is `false` for trait methods without default
    /// implementations).
    #[value(self.defaultness(s.base().tcx).has_value())]
    pub has_value: bool,
    pub fn_has_self_parameter: bool,
    pub opt_rpitit_info: Option<ImplTraitInTraitData>,
}

/// Reflects [`rustc_middle::ty::ImplTraitInTraitData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::ty::ImplTraitInTraitData, state: S as _s)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImplTraitInTraitData {
    Trait {
        fn_def_id: DefId,
        opaque_def_id: DefId,
    },
    Impl {
        fn_def_id: DefId,
    },
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssocItemContainer {
    TraitContainer {
        trait_id: DefId,
    },
    TraitImplContainer {
        impl_id: DefId,
        implemented_trait: DefId,
        implemented_trait_item: DefId,
        /// Whether the corresponding trait item had a default (and therefore this one overrides
        /// it).
        overrides_default: bool,
    },
    InherentImplContainer {
        impl_id: DefId,
    },
}

/// Reflects [`rustc_middle::ty::AssocKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_middle::ty::AssocKind, state: S as _tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssocKind {
    Const,
    Fn,
    Type,
}
