use crate::prelude::*;

/// The subset of [Expr] that corresponds to constants.
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub enum ConstantExprKind {
    Literal(LitKind),
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
    Borrow(ConstantExpr),
    ConstRef {
        id: ParamConst,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
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
            Literal(kind) => ExprKind::Literal {
                lit: Spanned {
                    span: c.span.clone(),
                    node: kind,
                },
                neg: false,
            },
            Adt { info, fields } => ExprKind::Adt(AdtExpr {
                info,
                fields: fields.into_iter().map(|field| field.into()).collect(),
                base: None,
                user_ty: None,
            }),
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
        };
        Decorated {
            contents: Box::new(kind),
            ..c
        }
    }
}

// #[tracing::instrument(skip(s))]
pub(crate) fn scalar_int_to_lit_kind<'tcx, S: BaseState<'tcx>>(
    s: &S,
    x: rustc_middle::ty::ScalarInt,
    ty: rustc_middle::ty::Ty,
) -> LitKind {
    use rustc_middle::ty;
    match ty.kind() {
        ty::Char => LitKind::Char(
            x.try_to_u8()
                .expect("scalar_int_to_lit_kind: expected a char")
                .into(),
        ),
        ty::Bool => LitKind::Bool(
            x.try_to_bool()
                .expect("scalar_int_to_lit_kind: expected a bool"),
        ),
        ty::Int(kind) => LitKind::Int(x.assert_bits(x.size()), LitIntType::Signed(kind.sinto(s))),
        ty::Uint(kind) => {
            LitKind::Int(x.assert_bits(x.size()), LitIntType::Unsigned(kind.sinto(s)))
        }
        _ => fatal!(
            s,
            "scalar_int_to_lit_kind: the type {:?} is not a literal",
            ty
        ),
    }
}

// TODO: This function is not used for now, but will be for Mir translation
#[allow(dead_code)]
pub(crate) fn translate_constant_integer_like_value<'tcx, S: BaseState<'tcx>>(
    ty: rustc_middle::ty::Ty<'tcx>,
    s: &S,
    scalar: &rustc_middle::mir::interpret::Scalar,
    span: rustc_span::Span,
) -> ConstantExpr {
    use rustc_middle::mir::Mutability;
    use rustc_middle::ty;
    let cspan = span.sinto(s);
    let kind = match ty.kind() {
        ty::Char | ty::Bool | ty::Int(_) | ty::Uint(_) => {
            let scalar_int = scalar.try_to_int().unwrap_or_else(|_| {
                span_fatal!(
                    s,
                    span,
                    "Type is primitive, but the scalar {:#?} is not a [Int]",
                    scalar
                )
            });
            ConstantExprKind::Literal(scalar_int_to_lit_kind(s, scalar_int, ty))
        }
        ty::Ref(region, ty, Mutability::Not) if region.is_erased() => {
            let tcx = s.base().tcx;
            let pointer = scalar.to_pointer(&tcx).unwrap_or_else(|_| {
                span_fatal!(
                    s,
                    span,
                    "Type is [Ref], but the scalar {:#?} is not a [Pointer]",
                    scalar
                )
            });
            let provenance = tcx.global_alloc(pointer.provenance.unwrap());
            use rustc_middle::mir::interpret::GlobalAlloc;
            let GlobalAlloc::Static(did) = provenance else {
                span_fatal!(
                    s,
                    span,
                    "Expected provenance to be GlobalAlloc::Static, got {:#?} instead",
                    provenance
                )
            };
            ConstantExprKind::Borrow(Decorated {
                ty: ty.sinto(s),
                span: cspan.clone(),
                contents: Box::new(ConstantExprKind::GlobalName { id: did.sinto(s) }),
                hir_id: None,
                attributes: vec![],
            })
        }
        // A [Scalar] might also be any zero-sized [Adt] or [Tuple]
        ty::Tuple(ty) if ty.is_empty() => ConstantExprKind::Tuple { fields: vec![] },
        ty::Adt(def, _) if let [variant_def] = &def.variants().raw && variant_def.fields.is_empty() => {
            ConstantExprKind::Adt{
                info: get_variant_information(def, &variant_def.def_id, s),
                fields: vec![],
            }
        },
        _ => span_fatal!(s, span, "Unexpected type {:#?} for scalar {:#?}", ty, scalar),
    };
    Decorated {
        ty: ty.sinto(s),
        span: cspan,
        contents: Box::new(kind),
        hir_id: None,
        attributes: vec![],
    }
}

pub(crate) fn const_to_constant_expr<'tcx, S: BaseState<'tcx>>(
    s: &S,
    c: rustc_middle::ty::Const<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    span: rustc_span::Span,
) -> ConstantExpr {
    use rustc_middle::ty;
    let kind = match c.kind() {
        ty::ConstKind::Param(p) => ConstantExprKind::ConstRef { id: p.sinto(s) },
        ty::ConstKind::Infer(..) => span_fatal!(s, span, "ty::ConstKind::Infer node? {:#?}", c),
        ty::ConstKind::Unevaluated(..) => {
            span_fatal!(s, span, "ty::ConstKind::Unevaluated node? {:#?}", c)
        }
        ty::ConstKind::Value(valtree) => return valtree_to_constant_expr(s, valtree, ty, span),
        ty::ConstKind::Error(_) => span_fatal!(s, span, "ty::ConstKind::Error"),
        ty::ConstKind::Expr(e) => {
            span_fatal!(s, span, "ty::ConstKind::Expr {:#?}", e)
        }
        ty::ConstKind::Bound(i, bound) => {
            supposely_unreachable!("ty::ConstKind::Bound": i, bound, ty);
            span_fatal!(s, span, "ty::ConstKind::Bound")
        }
        _ => span_fatal!(s, span, "unexpected case"),
    };
    Decorated {
        ty: ty.sinto(s),
        span: span.sinto(s),
        contents: Box::new(kind),
        hir_id: None,
        attributes: vec![],
    }
}

// #[tracing::instrument(skip(s))]
pub(crate) fn valtree_to_constant_expr<'tcx, S: BaseState<'tcx>>(
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
            LitKind::ByteStr(valtrees.into_iter().map(|x| match x {
                ty::ValTree::Leaf(leaf) => leaf.try_to_u8().unwrap_or_else(|e| span_fatal!(s, span, "Expected a u8 leaf while translating a str literal, got something else. Error: {:#?}", e)),
                _ => span_fatal!(s, span, "Expected a flat list of leaves while translating a str literal, got a arbitrary valtree.")
            }).collect(), StrStyle::Cooked)
        ),
        (ty::ValTree::Branch(_), ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) => {
            let contents: rustc_middle::ty::DestructuredConst = s
                .base().tcx
                .destructure_const(s.base().tcx.mk_const(valtree.clone(), ty));
            let fields = contents.fields.iter().copied();
            match ty.kind() {
                ty::Array(inner_ty, _) => ConstantExprKind::Array {
                    fields: fields
                        .map(|field| const_to_constant_expr(s, field, *inner_ty, span))
                        .collect(),
                },
                ty::Tuple(typs) => ConstantExprKind::Tuple {
                    fields: fields
                        .zip(typs.into_iter())
                        .map(|(field, inner_ty)| const_to_constant_expr(s, field, inner_ty, span))
                        .collect(),
                },
                ty::Adt(def, substs) => {
                    let variant_idx = contents
                        .variant
                        .expect("destructed const of adt without variant idx");
                    let variant_def = &def.variant(variant_idx);
                    ConstantExprKind::Adt{
                        info: get_variant_information(def, &variant_def.def_id, s),
                        fields: fields
                            .zip(&variant_def.fields)
                            .map(|(value, field)| ConstantFieldExpr {
                                field: field.did.sinto(s),
                                value: const_to_constant_expr(s, value, field.ty(s.base().tcx, substs), span),
                            })
                            .collect(),
                    }
                }
                _ => unreachable!(),
            }
        }
        (ty::ValTree::Leaf(x), _) => ConstantExprKind::Literal (
            scalar_int_to_lit_kind(s, x, ty)
        ),
        _ => span_fatal!(
            s,
            span,
            "valtree_to_expr: cannot handle valtree{:#?} ty={:#?}",
            valtree,
            ty
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
