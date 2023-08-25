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
        /// Variant index
        vid: Option<VariantIdx>,
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
                let kind = match lit {
                    Bool(b) => LitKind::Bool(b),
                    Char(c) => LitKind::Char(c),
                    Int(i) => {
                        // This is slightly tricky, especially because
                        // of the `neg` boolean. Doing nothing for now:
                        // we have to test.
                        let kind = ExprKind::Todo(format!(
                            "Todo: int ConstantLiteral::Int to Expr: {:?}",
                            i
                        ));
                        return Decorated {
                            contents: Box::new(kind),
                            ..c
                        };
                    }
                    ByteStr(raw, str_style) => LitKind::ByteStr(raw, str_style),
                };
                ExprKind::Literal {
                    lit: Spanned {
                        span: c.span.clone(),
                        node: kind,
                    },
                    neg: false,
                }
            }
            Adt {
                info,
                vid: _,
                fields,
            } => ExprKind::Adt(AdtExpr {
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
                .expect("scalar_int_to_constant_literal: expected a char")
                .into(),
        ),
        ty::Bool => ConstantLiteral::Bool(
            x.try_to_bool()
                .expect("scalar_int_to_constant_literal: expected a bool"),
        ),
        ty::Int(kind) => {
            let v = x.try_to_int(x.size()).unwrap();
            ConstantLiteral::Int(ConstantInt::Int(v, kind.sinto(s)))
        }
        ty::Uint(kind) => {
            let v = x.try_to_uint(x.size()).unwrap();
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
                span_fatal!(
                    s,
                    span,
                    "Type is primitive, but the scalar {:#?} is not a [Int]",
                    scalar
                )
            });
            ConstantExprKind::Literal(scalar_int_to_constant_literal(s, scalar_int, ty))
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
        // A [Scalar] might also be any zero-sized [Adt] or [Tuple] (i.e., unit)
        ty::Tuple(ty) if ty.is_empty() => ConstantExprKind::Tuple { fields: vec![] },
        // It seems we can have ADTs when there is only one variant, and this variant doesn't have any fields.
        ty::Adt(def, _) if let [variant_def] = &def.variants().raw && variant_def.fields.is_empty() => {
            ConstantExprKind::Adt{
                info: get_variant_information(def, &variant_def.def_id, s),
                vid: Option::Some(0),
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

/// We evaluate the anonymous constants
pub(crate) fn must_evaluate_constant(id: &DefId) -> bool {
    let last = id.path.last().unwrap();
    if let DefPathItem::AnonConst = &last.data {
        // Anonymous constant: evaluate
        true
    } else {
        // Not an anonymous constant: do not evaluate
        false
    }
}

pub(crate) fn const_to_constant_expr<'tcx, S: BaseState<'tcx> + HasOwnerId>(
    s: &S,
    c: rustc_middle::ty::Const<'tcx>,
) -> ConstantExpr {
    use rustc_middle::query::Key;
    use rustc_middle::ty;

    // Evaluate the non-evaluated **anonymous constants**.
    let c = if let ty::ConstKind::Unevaluated(ucv) = c.kind() {
        let id: DefId = ucv.def.sinto(s);
        if must_evaluate_constant(&id) {
            // Anonymous constant: evaluate
            c.eval(s.base().tcx, get_param_env(s))
        } else {
            // Not an anonymous constant: do not evaluate
            c
        }
    } else {
        c
    };

    let span = c.default_span(s.base().tcx);
    let kind = match c.kind() {
        ty::ConstKind::Param(p) => ConstantExprKind::ConstRef { id: p.sinto(s) },
        ty::ConstKind::Infer(..) => span_fatal!(s, span, "ty::ConstKind::Infer node? {:#?}", c),
        ty::ConstKind::Unevaluated(ucv) => {
            // There are two possibilities:
            // - it is a top-level constant
            // - it is a trait constant
            match s.base().tcx.opt_associated_item(ucv.def) {
                None => {
                    // No associated item: top-level constant
                    let id = ucv.def.sinto(s);
                    ConstantExprKind::GlobalName { id }
                }
                Some(assoc) => {
                    // This must be a trait constant
                    assert!(assoc.trait_item_def_id.is_some());
                    todo!()
                }
            }
        }
        ty::ConstKind::Value(valtree) => return valtree_to_constant_expr(s, valtree, c.ty(), span),
        ty::ConstKind::Error(_) => span_fatal!(s, span, "ty::ConstKind::Error"),
        ty::ConstKind::Expr(e) => {
            span_fatal!(s, span, "ty::ConstKind::Expr {:#?}", e)
        }
        ty::ConstKind::Bound(i, bound) => {
            supposely_unreachable!("ty::ConstKind::Bound": i, bound, c.ty());
            span_fatal!(s, span, "ty::ConstKind::Bound")
        }
        _ => span_fatal!(s, span, "unexpected case"),
    };
    Decorated {
        ty: c.ty().sinto(s),
        span: span.sinto(s),
        contents: Box::new(kind),
        hir_id: None,
        attributes: vec![],
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
                ty::ValTree::Leaf(leaf) => leaf.try_to_u8().unwrap_or_else(|e| span_fatal!(s, span, "Expected a u8 leaf while translating a str literal, got something else. Error: {:#?}", e)),
                _ => span_fatal!(s, span, "Expected a flat list of leaves while translating a str literal, got a arbitrary valtree.")
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
                        .map(|field| const_to_constant_expr(s, field))
                        .collect(),
                },
                ty::Tuple(_) => ConstantExprKind::Tuple {
                    fields: fields
                        .map(|field| const_to_constant_expr(s, field))
                        .collect(),
                },
                ty::Adt(def, _) => {
                    let variant_idx = contents
                        .variant
                        .expect("destructed const of adt without variant idx");
                    let variant_def = &def.variant(variant_idx);
                    let mut fields_it = fields.into_iter();

                    // Retrieve the variant index, if it is an enumeration
                    let vid: Option<VariantIdx> = if def.is_enum() {
                        // According to the documentation: the first field
                        // gives the discriminant (i.e., the index of the
                        // variant)
                        let vid = fields_it.next().unwrap();
                        let vid = const_to_constant_expr(s, vid);
                        if let ConstantExprKind::Literal(ConstantLiteral::Int(ConstantInt::Uint(v, _))) = *vid.contents {
                            Option::Some(v as VariantIdx)
                        }
                        else {
                            span_fatal!(
                                s,
                                span,
                                "valtree_to_expr: cannot handle valtree{:#?} ty={:#?}",
                                valtree,
                                ty
                            )
                        }
                    }
                    else if def.is_struct() {
                        Option::None
                    }
                    else {
                        // Union case
                        span_fatal!(
                            s,
                            span,
                            "valtree_to_expr: cannot handle valtree{:#?} ty={:#?}",
                            valtree,
                            ty
                        )
                    };

                    let fields: Vec<ConstantFieldExpr> = fields_it
                            .zip(&variant_def.fields)
                            .map(|(value, field)| ConstantFieldExpr {
                                field: field.did.sinto(s),
                                value: const_to_constant_expr(s, value),
                            })
                        .collect();

                    ConstantExprKind::Adt{
                        info: get_variant_information(def, &variant_def.def_id, s),
                        vid,
                        fields,
                    }
                }
                _ => unreachable!(),
            }
        }
        (ty::ValTree::Leaf(x), _) => ConstantExprKind::Literal (
            scalar_int_to_constant_literal(s, x, ty)
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
        .unwrap();

    // Iterate over the fields, which should be values
    assert!(dc.variant.is_none());

    // The type should be tuple
    let hax_ty = ty.sinto(s);
    match &hax_ty {
        Ty::Tuple(_) => (),
        _ => {
            span_fatal!(s, span, "Expected the type to be tuple: {:?}", val)
        }
    };

    // The fields should be of the variant: [ConstantKind::Value]
    let fields: Vec<(ty::Ty, interpret::ConstValue)> = dc
        .fields
        .iter()
        .map(|f| (f.ty(), f.try_to_value(tcx).unwrap()))
        .collect();

    // Below: we are mutually recursive with [const_value_to_constant_expr],
    // which takes a [ConstantKind] as input (see `cvalue` above), but it should be
    // ok because we call it on a strictly smaller value.
    let fields: Vec<ConstantExpr> = fields
        .into_iter()
        .map(|(ty, f)| const_value_to_constant_expr(s, ty, f, span))
        .collect();
    let cv = ConstantExprKind::Tuple { fields };
    Decorated {
        ty: hax_ty,
        span: span.sinto(s),
        contents: Box::new(cv),
        hir_id: Option::None,
        attributes: Vec::new(),
    }
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
            let ty = ty.sinto(s);
            let cv = ConstantExprKind::Todo(format!("ConstValue::Slice: {:?}", val));
            Decorated {
                ty,
                span: span.sinto(s),
                contents: Box::new(cv),
                hir_id: Option::None,
                attributes: Vec::new(),
            }
        }
        ConstValue::ZeroSized { .. } => {
            // Should be unit
            let ty = ty.sinto(s);
            if let Ty::Tuple(tys) = &ty && tys.is_empty() {}
            else {
                span_fatal!(s, span, "Expected the type to be tuple: {:?}", val)
            }
            let cv = ConstantExprKind::Tuple { fields: Vec::new() };
            Decorated {
                ty,
                span: span.sinto(s),
                contents: Box::new(cv),
                hir_id: Option::None,
                attributes: Vec::new(),
            }
        }
    }
}
