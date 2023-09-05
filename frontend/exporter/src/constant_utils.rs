use crate::prelude::*;

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub enum ConstantInt {
    Int(i128, IntTy),
    Uint(u128, UintTy),
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub enum ConstantLiteral {
    // TODO: add Str, etc.
    Bool(bool),
    Char(char),
    Int(ConstantInt),
    ByteStr(Vec<u8>, StrStyle),
}

/// The subset of [Expr] that corresponds to constants.
#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub enum ConstantExprKind {
    Literal(ConstantLiteral),
    Adt {
        info: VariantInformations,
        fields: Vec<ConstantFieldExpr>,
    },
    Array {
        fields: Vec<ConstantExpr>,
    },
    Tuple {
        fields: Vec<ConstantExpr>,
    },
    GlobalName {
        id: GlobalIdent,
    },
    /// A trait constant
    ///
    /// Ex.:
    /// ```text
    /// impl Foo for Bar {
    ///   const C : usize = 32; // <-
    /// }
    /// ```
    TraitConst {
        impl_source: ImplSource,
        substs: Vec<GenericArg>,
        name: String,
    },
    Borrow(ConstantExpr),
    ConstRef {
        id: ParamConst,
    },
    Todo(String),
}

#[derive(
    Clone, Debug, Serialize, Deserialize, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord,
)]
pub struct ConstantFieldExpr {
    pub field: DefId,
    pub value: ConstantExpr,
}

pub type ConstantExpr = Decorated<ConstantExprKind>;

impl From<ConstantFieldExpr> for FieldExpr {
    fn from(c: ConstantFieldExpr) -> FieldExpr {
        FieldExpr {
            value: c.value.into(),
            field: c.field,
        }
    }
}

impl From<ConstantExpr> for Expr {
    fn from(c: ConstantExpr) -> Expr {
        use ConstantExprKind::*;
        let kind = match *c.contents {
            Literal(lit) => {
                use ConstantLiteral::*;
                let mut neg = false;
                let node = match lit {
                    Bool(b) => LitKind::Bool(b),
                    Char(c) => LitKind::Char(c),
                    Int(i) => {
                        use LitIntType::*;
                        match i {
                            ConstantInt::Uint(v, t) => LitKind::Int(v, Unsigned(t)),
                            ConstantInt::Int(v, t) => {
                                neg = v.is_negative();
                                LitKind::Int(v.abs_diff(0), Signed(t))
                            }
                        }
                    }
                    ByteStr(raw, str_style) => LitKind::ByteStr(raw, str_style),
                };
                let span = c.span.clone();
                let lit = Spanned { span, node };
                ExprKind::Literal { lit, neg }
            }
            Adt { info, fields } => ExprKind::Adt(AdtExpr {
                info,
                fields: fields.into_iter().map(|field| field.into()).collect(),
                base: None,
                user_ty: None,
            }),
            TraitConst { .. } => {
                // SH: I leave this for you Lucas
                unimplemented!()
            }
            GlobalName { id } => ExprKind::GlobalName { id },
            Borrow(e) => ExprKind::Borrow {
                borrow_kind: BorrowKind::Shared,
                arg: e.into(),
            },
            ConstRef { id } => ExprKind::ConstRef { id },
            Array { fields } => ExprKind::Array {
                fields: fields.into_iter().map(|field| field.into()).collect(),
            },
            Tuple { fields } => ExprKind::Tuple {
                fields: fields.into_iter().map(|field| field.into()).collect(),
            },
            Todo(msg) => ExprKind::Todo(msg),
        };
        Decorated {
            contents: Box::new(kind),
            ..c
        }
    }
}

pub(crate) fn scalar_int_to_constant_literal<'tcx, S: BaseState<'tcx>>(
    s: &S,
    x: rustc_middle::ty::ScalarInt,
    ty: rustc_middle::ty::Ty,
) -> ConstantLiteral {
    use rustc_middle::ty;
    match ty.kind() {
        ty::Char => ConstantLiteral::Char(
            char::try_from(x)
                .s_expect(s, "scalar_int_to_constant_literal: expected a char")
                .into(),
        ),
        ty::Bool => ConstantLiteral::Bool(
            x.try_to_bool()
                .s_expect(s, "scalar_int_to_constant_literal: expected a bool"),
        ),
        ty::Int(kind) => {
            let v = x.try_to_int(x.size()).s_unwrap(s);
            ConstantLiteral::Int(ConstantInt::Int(v, kind.sinto(s)))
        }
        ty::Uint(kind) => {
            let v = x.try_to_uint(x.size()).s_unwrap(s);
            ConstantLiteral::Int(ConstantInt::Uint(v, kind.sinto(s)))
        }
        _ => fatal!(
            s,
            "scalar_int_to_constant_literal: the type {:?} is not a literal",
            ty
        ),
    }
}

pub(crate) fn scalar_to_constant_expr<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    ty: rustc_middle::ty::Ty<'tcx>,
    scalar: &rustc_middle::mir::interpret::Scalar,
    span: rustc_span::Span,
) -> ConstantExpr {
    use rustc_middle::mir::Mutability;
    use rustc_middle::ty;
    let cspan = span.sinto(s);
    // The documentation explicitly says not to match on a scalar.
    // We match on the type and use it to convert the value.
    let kind = match ty.kind() {
        ty::Char | ty::Bool | ty::Int(_) | ty::Uint(_) => {
            let scalar_int = scalar.try_to_int().unwrap_or_else(|_| {
                fatal!(
                    s[span],
                    "Type is primitive, but the scalar {:#?} is not a [Int]",
                    scalar
                )
            });
            ConstantExprKind::Literal(scalar_int_to_constant_literal(s, scalar_int, ty))
        }
        ty::Ref(region, ty, Mutability::Not) if region.is_erased() => {
            let tcx = s.base().tcx;
            let pointer = scalar.to_pointer(&tcx).unwrap_or_else(|_| {
                fatal!(
                    s[span],
                    "Type is [Ref], but the scalar {:#?} is not a [Pointer]",
                    scalar
                )
            });
            let provenance = tcx.global_alloc(pointer.provenance.s_unwrap(s));
            use rustc_middle::mir::interpret::GlobalAlloc;
            let GlobalAlloc::Static(did) = provenance else {
                fatal!(
                    s[span],
                    "Expected provenance to be GlobalAlloc::Static, got {:#?} instead",
                    provenance
                )
            };
            ConstantExprKind::Borrow((ConstantExprKind::GlobalName { id: did.sinto(s) }).decorate(ty.sinto(s), cspan.clone()))
        }
        // A [Scalar] might also be any zero-sized [Adt] or [Tuple] (i.e., unit)
        ty::Tuple(ty) if ty.is_empty() => ConstantExprKind::Tuple { fields: vec![] },
        // It seems we can have ADTs when there is only one variant, and this variant doesn't have any fields.
        ty::Adt(def, _) if let [variant_def] = &def.variants().raw && variant_def.fields.is_empty() => {
            ConstantExprKind::Adt{
                info: get_variant_information(def, rustc_abi::FIRST_VARIANT, s),
                fields: vec![],
            }
        },
        _ => fatal!(s[span], "Unexpected type {:#?} for scalar {:#?}", ty, scalar),
    };
    kind.decorate(ty.sinto(s), cspan)
}

/// Whether a `DefId` is a `AnonConst`. An anonymous constant is
/// generated by Rustc, hoisting every constat bits from items as
/// separate top-level items. This AnonConst mechanism is internal to
/// Rustc; we don't want to reflect that, instead we prefer inlining
/// those. `is_anon_const` is used to detect such AnonConst so that we
/// can evaluate and inline them.
pub(crate) fn is_anon_const<'tcx>(
    did: rustc_span::def_id::DefId,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> bool {
    matches!(
        tcx.def_path(did).data.last().map(|x| x.data),
        Some(rustc_hir::definitions::DefPathData::AnonConst)
    )
}

impl ConstantExprKind {
    pub fn decorate(self, ty: Ty, span: Span) -> Decorated<Self> {
        Decorated {
            contents: Box::new(self),
            hir_id: None,
            attributes: vec![],
            ty,
            span,
        }
    }
}

pub enum TranslateUnevalRes<T> {
    GlobalName(ConstantExprKind),
    EvaluatedConstant(T),
}

pub(crate) fn trait_const_to_constant_expr_kind<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    const_def_id: rustc_hir::def_id::DefId,
    substs: rustc_middle::ty::SubstsRef<'tcx>,
    assoc: &rustc_middle::ty::AssocItem,
) -> ConstantExprKind {
    assert!(assoc.trait_item_def_id.is_some());
    let name = assoc.name.to_string();

    // Retrieve the trait information
    let (mut substs, trait_info) = get_trait_info(s, const_def_id, substs, assoc);

    // Truncate the substitution to keep what is relevant to the const (and
    // remove the arguments which actually apply to the trait instance)
    let substs = substs.split_off(trait_info.params_info.num_generic_params);

    ConstantExprKind::TraitConst {
        impl_source: trait_info.impl_source,
        substs,
        name,
    }
}

pub trait ConstantExt<'tcx>: Sized + std::fmt::Debug {
    fn eval_constant<S: BaseState<'tcx>>(&self, s: &S) -> Option<Self>;

    /// Performs a one-step translation of a constant.
    ///  - When a constant refers to a named top-level constant, we want to use that, thus we translate the constant to a `ConstantExprKind::GlobalName`. This is captured by the variant `TranslateUnevalRes::GlobalName`.
    ///  - When a constant refers to a anonymous top-level constant, we evaluate it. If the evaluation fails, we report an error: we expect every AnonConst to be reducible. Otherwise, we return the variant `TranslateUnevalRes::EvaluatedConstant`.

    // TODO after meging `fast` in: 6a074cf19785b3a3718a6f863a32cfb893f3cc6b + 269b625aab173d0297cb6a8371677f83800cbf40
    fn translate_uneval(
        &self,
        s: &impl BaseState<'tcx>,
        ucv: rustc_middle::ty::UnevaluatedConst,
    ) -> TranslateUnevalRes<Self> {
        let tcx = s.base().tcx;
        if is_anon_const(ucv.def, tcx) {
            TranslateUnevalRes::EvaluatedConstant(self.eval_constant(s).unwrap_or_else(|| {
                supposely_unreachable_fatal!(s, "TranslateUneval"; {self, ucv});
            }))
        } else {
            let id = ucv.def.sinto(s);
            TranslateUnevalRes::GlobalName(ConstantExprKind::GlobalName { id })
        }
    }
}
impl<'tcx> ConstantExt<'tcx> for rustc_middle::ty::Const<'tcx> {
    fn eval_constant<S: BaseState<'tcx>>(&self, s: &S) -> Option<Self> {
        let evaluated = self.eval(s.base().tcx, get_param_env(s));
        (&evaluated != self).then_some(evaluated)
    }
}
impl<'tcx> ConstantExt<'tcx> for rustc_middle::mir::ConstantKind<'tcx> {
    fn eval_constant<S: BaseState<'tcx>>(&self, s: &S) -> Option<Self> {
        let evaluated = self.eval(s.base().tcx, get_param_env(s));
        (&evaluated != self).then_some(evaluated)
    }
}
impl<'tcx, S: BaseState<'tcx> + HasOwnerId> SInto<S, ConstantExpr>
    for rustc_middle::ty::Const<'tcx>
{
    fn sinto(&self, s: &S) -> ConstantExpr {
        use rustc_middle::{query::Key, ty};
        let span = self.default_span(s.base().tcx);
        let kind = match self.kind() {
            ty::ConstKind::Param(p) => ConstantExprKind::ConstRef { id: p.sinto(s) },
            ty::ConstKind::Infer(..) => fatal!(s[span], "ty::ConstKind::Infer node? {:#?}", self),

            ty::ConstKind::Unevaluated(ucv) => match self.translate_uneval(s, ucv) {
                TranslateUnevalRes::EvaluatedConstant(c) => return c.sinto(s),
                TranslateUnevalRes::GlobalName(c) => c,
            },
            ty::ConstKind::Value(valtree) => {
                return valtree_to_constant_expr(s, valtree, self.ty(), span)
            }
            ty::ConstKind::Error(_) => fatal!(s[span], "ty::ConstKind::Error"),
            ty::ConstKind::Expr(e) => fatal!(s[span], "ty::ConstKind::Expr {:#?}", e),

            ty::ConstKind::Bound(i, bound) => {
                supposely_unreachable_fatal!(s[span], "ty::ConstKind::Bound"; {i, bound, self.ty()});
            }
            _ => fatal!(s[span], "unexpected case"),
        };
        kind.decorate(self.ty().sinto(s), span.sinto(s))
    }
}

// #[tracing::instrument(skip(s))]
pub(crate) fn valtree_to_constant_expr<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    valtree: rustc_middle::ty::ValTree<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    span: rustc_span::Span,
) -> ConstantExpr {
    use rustc_middle::ty;
    let kind = match (valtree, ty.kind()) {
        (_, ty::Ref(_, inner_ty, _)) => {
            ConstantExprKind::Borrow(valtree_to_constant_expr(s, valtree, *inner_ty, span))
        }
        (ty::ValTree::Branch(valtrees), ty::Str) => ConstantExprKind::Literal(
            ConstantLiteral::ByteStr(valtrees.iter().map(|x| match x {
                ty::ValTree::Leaf(leaf) => leaf.try_to_u8().unwrap_or_else(|e| fatal!(s[span], "Expected a u8 leaf while translating a str literal, got something else. Error: {:#?}", e)),
                _ => fatal!(s[span], "Expected a flat list of leaves while translating a str literal, got a arbitrary valtree.")
            }).collect(), StrStyle::Cooked))
        ,
        (ty::ValTree::Branch(_), ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) => {
            let contents: rustc_middle::ty::DestructuredConst = s
                .base().tcx
                .destructure_const(s.base().tcx.mk_const(valtree, ty));
            let fields = contents.fields.iter().copied();
            match ty.kind() {
                ty::Array(_, _) => ConstantExprKind::Array {
                    fields: fields
                        .map(|field| field.sinto(s))
                        .collect(),
                },
                ty::Tuple(_) => ConstantExprKind::Tuple {
                    fields: fields
                        .map(|field| field.sinto(s))
                        .collect(),
                },
                ty::Adt(def, _) => {
                    let variant_idx = contents
                        .variant
                        .s_expect(s, "destructed const of adt without variant idx");
                    let variant_def = &def.variant(variant_idx);

                    ConstantExprKind::Adt{
                        info: get_variant_information(def, variant_idx, s),
                        fields: fields.into_iter()
                            .zip(&variant_def.fields)
                            .map(|(value, field)| ConstantFieldExpr {
                                field: field.did.sinto(s),
                                value: value.sinto(s),
                            })
                        .collect(),
                    }
                }
                _ => unreachable!(),
            }
        }
        (ty::ValTree::Leaf(x), _) => ConstantExprKind::Literal (
            scalar_int_to_constant_literal(s, x, ty)
        ),
        _ => supposely_unreachable_fatal!(
            s[span], "valtree_to_expr";
            {valtree, ty}
        ),
    };
    kind.decorate(ty.sinto(s), span.sinto(s))
}

pub(crate) fn const_value_reference_to_constant_expr<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    ty: rustc_middle::ty::Ty<'tcx>,
    val: rustc_middle::mir::interpret::ConstValue<'tcx>,
    span: rustc_span::Span,
) -> ConstantExpr {
    use rustc_middle::mir::interpret;
    use rustc_middle::ty;

    let tcx = s.base().tcx;

    // We use [try_destructure_mir_constant] to destructure the constant
    let param_env = get_param_env(s);
    // We have to clone some values: it is a bit annoying, but I don't
    // manage to get the lifetimes working otherwise...
    let cvalue = rustc_middle::mir::ConstantKind::Val(val, ty);
    let param_env_and_const = rustc_middle::ty::ParamEnvAnd {
        param_env,
        value: cvalue,
    };

    let dc = tcx
        .try_destructure_mir_constant(param_env_and_const)
        .s_unwrap(s);

    // Iterate over the fields, which should be values
    assert!(dc.variant.is_none());

    // The type should be tuple
    let hax_ty = ty.sinto(s);
    match &hax_ty {
        Ty::Tuple(_) => (),
        _ => {
            fatal!(s[span], "Expected the type to be tuple: {:?}", val)
        }
    };

    // The fields should be of the variant: [ConstantKind::Value]
    let fields: Vec<(ty::Ty, interpret::ConstValue)> = dc
        .fields
        .iter()
        .map(|f| (f.ty(), f.try_to_value(tcx).s_unwrap(s)))
        .collect();

    // Below: we are mutually recursive with [const_value_to_constant_expr],
    // which takes a [ConstantKind] as input (see `cvalue` above), but it should be
    // ok because we call it on a strictly smaller value.
    let fields: Vec<ConstantExpr> = fields
        .into_iter()
        .map(|(ty, f)| const_value_to_constant_expr(s, ty, f, span))
        .collect();
    (ConstantExprKind::Tuple { fields }).decorate(hax_ty, span.sinto(s))
}

pub fn const_value_to_constant_expr<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    ty: rustc_middle::ty::Ty<'tcx>,
    val: rustc_middle::mir::interpret::ConstValue<'tcx>,
    span: rustc_span::Span,
) -> ConstantExpr {
    use rustc_middle::mir::interpret::ConstValue;
    match val {
        ConstValue::Scalar(scalar) => scalar_to_constant_expr(s, ty, &scalar, span),
        ConstValue::ByRef { .. } => const_value_reference_to_constant_expr(s, ty, val, span),
        ConstValue::Slice { .. } => {
            (ConstantExprKind::Todo(format!("ConstValue::Slice: {:?}", val)))
                .decorate(ty.sinto(s), span.sinto(s))
        }
        ConstValue::ZeroSized { .. } => {
            let ty = ty.sinto(s);
            let is_ty_unit = matches!(&ty, Ty::Tuple(tys) if tys.is_empty());
            if !is_ty_unit {
                supposely_unreachable_fatal!(s[span], "ExpectedTyUnit"; {val, ty});
            }
            (ConstantExprKind::Tuple { fields: vec![] }).decorate(ty, span.sinto(s))
        }
    }
}
