use crate::prelude::*;

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::mir::MirPhase, state: S as s)]
pub enum MirPhase {
    Built,
    Analysis(AnalysisPhase),
    Runtime(RuntimePhase),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_middle::mir::LocalDecl<'tcx>, state: S as s)]
pub struct LocalDecl {
    pub mutability: Mutability,
    pub local_info: ClearCrossCrate<LocalInfo>,
    pub internal: bool,
    pub ty: Ty,
    pub user_ty: Option<UserTypeProjections>,
    pub source_info: SourceInfo,
    #[not_in_source]
    #[map(None)]
    pub name: Option<String>, // This information is contextual, thus the SInto instance initializes it to None, and then we fill it while `SInto`ing MirBody
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ClearCrossCrate<T> {
    Clear,
    Set(T),
}

impl<S, TT, T: SInto<S, TT>> SInto<S, ClearCrossCrate<TT>>
    for rustc_middle::mir::ClearCrossCrate<T>
{
    fn sinto(&self, s: &S) -> ClearCrossCrate<TT> {
        match self {
            rustc_middle::mir::ClearCrossCrate::Clear => ClearCrossCrate::Clear,
            rustc_middle::mir::ClearCrossCrate::Set(x) => ClearCrossCrate::Set(x.sinto(s)),
        }
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::mir::RuntimePhase, state: S as _s)]
pub enum RuntimePhase {
    Initial,
    PostCleanup,
    Optimized,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<S>, from: rustc_middle::mir::AnalysisPhase, state: S as _s)]
pub enum AnalysisPhase {
    Initial,
    PostCleanup,
}

pub type BasicBlocks = IndexVec<BasicBlock, BasicBlockData>;

fn name_of_local(
    local: rustc_middle::mir::Local,
    var_debug_info: &Vec<rustc_middle::mir::VarDebugInfo>,
) -> Option<String> {
    var_debug_info
        .into_iter()
        .find(|info| {
            if let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value {
                place.projection.is_empty() && place.local == local
            } else {
                false
            }
        })
        .map(|dbg| dbg.name.to_ident_string())
}

/// Enumerates the kinds of Mir bodies. TODO: use const generics
/// instead of an open list of types.
pub mod mir_kinds {
    use crate::prelude::{Deserialize, JsonSchema, Serialize};
    use rustc_data_structures::steal::Steal;
    use rustc_middle::mir::Body;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::def_id::LocalDefId;
    pub trait IsMirKind: Clone {
        fn get_mir<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> &'tcx Steal<Body<'tcx>>;
    }
    #[derive(Clone, Copy, Debug, JsonSchema, Serialize, Deserialize)]
    pub struct Const;
    impl IsMirKind for Const {
        fn get_mir<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> &'tcx Steal<Body<'tcx>> {
            tcx.mir_const(id)
        }
    }
    #[derive(Clone, Copy, Debug, JsonSchema, Serialize, Deserialize)]
    pub struct Built;
    impl IsMirKind for Built {
        fn get_mir<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> &'tcx Steal<Body<'tcx>> {
            tcx.mir_built(id)
        }
    }
    // TODO: Add [Promoted] MIR
}
pub use mir_kinds::IsMirKind;

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Body<'tcx>, state: S as s)]
pub struct MirBody<KIND> {
    #[map(x.clone().as_mut().sinto(s))]
    pub basic_blocks: BasicBlocks,
    pub phase: MirPhase,
    pub pass_count: usize,
    pub source: MirSource,
    pub source_scopes: IndexVec<SourceScope, SourceScopeData>,
    pub generator: Option<GeneratorInfo>,
    #[map({
        let mut local_decls: rustc_index::IndexVec<rustc_middle::mir::Local, LocalDecl> = x.iter().map(|local_decl| {
            local_decl.sinto(s)
        }).collect();
        local_decls.iter_enumerated_mut().for_each(|(local, local_decl)| {
            local_decl.name = name_of_local(local, &self.var_debug_info);
        });
        let local_decls: rustc_index::IndexVec<Local, LocalDecl> = local_decls.into_iter().collect();
        local_decls.into()
    })]
    pub local_decls: IndexVec<Local, LocalDecl>,
    pub user_type_annotations: CanonicalUserTypeAnnotations,
    pub arg_count: usize,
    pub spread_arg: Option<Local>,
    pub var_debug_info: Vec<VarDebugInfo>,
    pub span: Span,
    pub required_consts: Vec<Constant>,
    pub is_polymorphic: bool,
    pub injection_phase: Option<MirPhase>,
    pub tainted_by_errors: Option<ErrorGuaranteed>,
    #[not_in_source]
    #[map(std::marker::PhantomData)]
    pub _kind: std::marker::PhantomData<KIND>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Operand<'tcx>, state: S as s)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Terminator<'tcx>, state: S as s)]
pub struct Terminator {
    pub source_info: SourceInfo,
    pub kind: TerminatorKind,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx>+ HasMir<'tcx>>, from: rustc_middle::mir::TerminatorKind<'tcx>, state: S as s)]
pub enum TerminatorKind {
    Goto {
        target: BasicBlock,
    },
    SwitchInt {
        discr: Operand,
        targets: SwitchTargets,
    },
    Resume,
    Terminate,
    Return,
    Unreachable,
    Drop {
        place: Place,
        target: BasicBlock,
        unwind: UnwindAction,
        replace: bool,
    },
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: Place,
        target: Option<BasicBlock>,
        unwind: UnwindAction,
        from_hir_call: bool,
        fn_span: Span,
    },
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertMessage,
        target: BasicBlock,
        unwind: UnwindAction,
    },
    Yield {
        value: Operand,
        resume: BasicBlock,
        resume_arg: Place,
        drop: Option<BasicBlock>,
    },
    GeneratorDrop,
    FalseEdge {
        real_target: BasicBlock,
        imaginary_target: BasicBlock,
    },
    FalseUnwind {
        real_target: BasicBlock,
        unwind: UnwindAction,
    },
    InlineAsm {
        template: Vec<InlineAsmTemplatePiece>,
        operands: Vec<InlineAsmOperand>,
        options: InlineAsmOptions,
        line_spans: Vec<Span>,
        destination: Option<BasicBlock>,
        unwind: UnwindAction,
    },
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Statement<'tcx>, state: S as s)]
pub struct Statement {
    pub source_info: SourceInfo,
    #[map(Box::new(x.sinto(s)))]
    pub kind: Box<StatementKind>,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::StatementKind<'tcx>, state: S as s)]
pub enum StatementKind {
    Assign((Place, Rvalue)),
    FakeRead((FakeReadCause, Place)),
    SetDiscriminant {
        place: Place,
        variant_index: VariantIdx,
    },
    Deinit(Place),
    StorageLive(Local),
    StorageDead(Local),
    Retag(RetagKind, Place),
    PlaceMention(Place),
    AscribeUserType((Place, UserTypeProjection), Variance),
    Coverage(Coverage),
    Intrinsic(NonDivergingIntrinsic),
    ConstEvalCounter,
    Nop,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Place {
    pub ty: Ty,
    pub kind: PlaceKind,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum PlaceKind {
    Local(Local),
    Projection {
        place: Box<Place>,
        kind: ProjectionElem,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ProjectionElemFieldKind {
    Tuple(u32),
    Ast {
        variant: DefId,
        typ: DefId,
        index: FieldIdx,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ProjectionElem {
    Deref,
    Field(ProjectionElemFieldKind),
    Index(Local),
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    Downcast(Option<Symbol>, VariantIdx),
    OpaqueCast,
}

// refactor
impl<'tcx, S: BaseState<'tcx> + HasMir<'tcx>> SInto<S, Place> for rustc_middle::mir::Place<'tcx> {
    #[tracing::instrument(level = "info", skip(s))]
    fn sinto(&self, s: &S) -> Place {
        let local_decl = &s.mir().local_decls[self.local];
        let mut current_ty: rustc_middle::ty::Ty = local_decl.ty;
        let mut current_kind = PlaceKind::Local(self.local.sinto(s));
        let mut elems: &[rustc_middle::mir::PlaceElem] = self.projection.as_slice();

        loop {
            use rustc_middle::mir::ProjectionElem::*;
            let cur_ty = current_ty.clone();
            let cur_kind = current_kind.clone();
            let mk_field = |index: &rustc_abi::FieldIdx,
                            variant_idx: Option<rustc_abi::VariantIdx>| {
                ProjectionElem::Field(match cur_ty.kind() {
                    rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
                        let variant_idx = variant_idx.unwrap_or_else(|| {
                            if adt_def.is_struct() {
                                rustc_abi::VariantIdx::from_usize(0)
                            } else {
                                supposely_unreachable_fatal!(
                                    s, "CallNotTyFnDef";
                                    {index, adt_def, substs, variant_idx, &cur_ty, &cur_kind}
                                )
                            }
                        });
                        ProjectionElemFieldKind::Ast {
                            typ: adt_def.did().sinto(s),
                            variant: adt_def.variant(variant_idx.clone()).def_id.sinto(s),
                            index: index.sinto(s),
                        }
                    }
                    rustc_middle::ty::TyKind::Tuple(_types) => {
                        ProjectionElemFieldKind::Tuple(index.as_u32())
                    }
                    ty_kind => {
                        supposely_unreachable_fatal!(
                            s, "ProjectionElemFieldBadType";
                            {index, variant_idx, ty_kind, &cur_ty, &cur_kind}
                        )
                    }
                })
            };
            let elem_kind: ProjectionElem = match elems {
                [Downcast(_, variant_idx), Field(index, ty), rest @ ..] => {
                    elems = rest;
                    let r = mk_field(index, Some(*variant_idx));
                    current_ty = ty.clone();
                    r
                }
                [elem, rest @ ..] => {
                    elems = rest;
                    use rustc_middle::ty::TyKind;
                    match elem {
                        Deref => {
                            current_ty = match current_ty.kind() {
                                TyKind::Ref(_, ty, _) => ty.clone(),
                                TyKind::Adt(def, substs) if def.is_box() => substs.type_at(0),
                                _ => supposely_unreachable_fatal!(
                                    s, "PlaceDerefNotRefNorBox";
                                    {current_ty, current_kind, elem}
                                ),
                            };
                            ProjectionElem::Deref
                        }
                        Field(index, ty) => {
                            let r = mk_field(index, None);
                            current_ty = ty.clone();
                            r
                        }
                        Index(local) => {
                            let (TyKind::Slice(ty) | TyKind::Array(ty, _)) = current_ty.kind() else {
                                supposely_unreachable_fatal!(
                                    s, "PlaceIndexNotSlice";
                                    {current_ty, current_kind, elem}
                                )
                            };
                            current_ty = ty.clone();
                            ProjectionElem::Index(local.sinto(s))
                        }
                        ConstantIndex {
                            offset,
                            min_length,
                            from_end,
                        } => {
                            let TyKind::Slice(ty) = current_ty.kind() else {
                                supposely_unreachable_fatal!(
                                    s, "PlaceConstantIndexNotSlice";
                                    {current_ty, current_kind, elem}
                                )
                            };
                            current_ty = ty.clone();
                            ProjectionElem::ConstantIndex {
                                offset: *offset,
                                min_length: *min_length,
                                from_end: *from_end,
                            }
                        }
                        Subslice { from, to, from_end } =>
                        // TODO: We assume subslice preserves the type
                        {
                            ProjectionElem::Subslice {
                                from: *from,
                                to: *to,
                                from_end: *from_end,
                            }
                        }
                        OpaqueCast(ty) => {
                            current_ty = ty.clone();
                            ProjectionElem::OpaqueCast
                        }
                        Downcast { .. } => panic!("unexpected Downcast"),
                    }
                }
                [] => break,
            };

            current_kind = PlaceKind::Projection {
                place: Box::new(Place {
                    ty: cur_ty.sinto(s),
                    kind: current_kind.clone(),
                }),
                kind: elem_kind,
            };
        }
        Place {
            ty: current_ty.sinto(s),
            kind: current_kind.clone(),
        }
    }
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::AggregateKind<'tcx>, state: S as s)]
pub enum AggregateKind {
    Array(Ty),
    Tuple,
    Adt(
        DefId,
        VariantIdx,
        Vec<GenericArg>,
        Option<UserTypeAnnotationIndex>,
        Option<FieldIdx>,
    ),
    Closure(DefId, Vec<GenericArg>),
    Generator(DefId, Vec<GenericArg>, Movability),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::CastKind, state: S as s)]
pub enum CastKind {
    PointerExposeAddress,
    PointerFromExposedAddress,
    Pointer(PointerCast),
    DynStar,
    IntToInt,
    FloatToInt,
    FloatToFloat,
    IntToFloat,
    PtrToPtr,
    FnPtrToPtr,
    Transmute,
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::NullOp<'tcx>, state: S as s)]
pub enum NullOp {
    SizeOf,
    AlignOf,
    OffsetOf(Vec<FieldIdx>),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::Rvalue<'tcx>, state: S as s)]
pub enum Rvalue {
    Use(Operand),
    Repeat(Operand, Const),
    Ref(Region, BorrowKind, Place),
    ThreadLocalRef(DefId),
    AddressOf(Mutability, Place),
    Len(Place),
    Cast(CastKind, Operand, Ty),
    BinaryOp(BinOp, (Operand, Operand)),
    CheckedBinaryOp(BinOp, (Operand, Operand)),
    NullaryOp(NullOp, Ty),
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
    Aggregate(AggregateKind, IndexVec<FieldIdx, Operand>),
    ShallowInitBox(Operand, Ty),
    CopyForDeref(Place),
}

#[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[args(<'tcx, S: BaseState<'tcx> + HasMir<'tcx>>, from: rustc_middle::mir::BasicBlockData<'tcx>, state: S as s)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
    pub is_cleanup: bool,
    // #[not_in_source]
    // #[map(panic!())]
    // pub hello: T,
}
// use hello::*;

pub type CanonicalUserTypeAnnotations =
    IndexVec<UserTypeAnnotationIndex, CanonicalUserTypeAnnotation>;

make_idx_wrapper!(rustc_middle::mir, BasicBlock);
make_idx_wrapper!(rustc_middle::mir, SourceScope);
make_idx_wrapper!(rustc_middle::mir, Local);
make_idx_wrapper!(rustc_middle::ty, UserTypeAnnotationIndex);
make_idx_wrapper!(rustc_abi, FieldIdx);

sinto_todo!(rustc_middle::mir, Constant<'tcx>);
sinto_todo!(rustc_middle::mir, SourceInfo);
sinto_todo!(rustc_middle::mir, UserTypeProjections);
sinto_todo!(rustc_middle::mir, LocalInfo<'tcx>);
sinto_todo!(rustc_ast::ast, InlineAsmTemplatePiece);
sinto_todo!(rustc_ast::ast, InlineAsmOptions);
sinto_todo!(rustc_middle::mir, InlineAsmOperand<'tcx>);
sinto_todo!(rustc_middle::mir, AssertMessage<'tcx>);
sinto_todo!(rustc_middle::mir, UnwindAction);
sinto_todo!(rustc_middle::mir, SwitchTargets);
sinto_todo!(rustc_middle::mir, SourceScopeData<'tcx>);
sinto_todo!(rustc_middle::mir, FakeReadCause);
sinto_todo!(rustc_middle::mir, RetagKind);
sinto_todo!(rustc_middle::mir, Coverage);
sinto_todo!(rustc_middle::mir, NonDivergingIntrinsic<'tcx>);
sinto_todo!(rustc_middle::mir, UserTypeProjection);
sinto_todo!(rustc_middle::mir, MirSource<'tcx>);
sinto_todo!(rustc_middle::mir, GeneratorInfo<'tcx>);
sinto_todo!(rustc_middle::mir, VarDebugInfo<'tcx>);
sinto_todo!(rustc_span, ErrorGuaranteed);
