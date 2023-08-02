use crate::prelude::*;

#[tracing::instrument(skip(state))]
pub(crate) fn arrow_of_sig<'tcx, S: BaseState<'tcx>>(
    sig: &rustc_middle::ty::PolyFnSig<'tcx>,
    state: &S,
) -> Ty {
    let tcx = state.base().tcx;
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

#[tracing::instrument(skip(s))]
pub(crate) fn scalar_int_to_literal<'tcx, S: BaseState<'tcx>>(
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
        _ => fatal!(
            s,
            "scalar_int_to_literal: the type {:?} is not a literal",
            ty
        ),
    }
}

#[tracing::instrument(skip(s))]
pub(crate) fn const_to_expr<'tcx, S: BaseState<'tcx>>(
    s: &S,
    c: rustc_middle::ty::Const<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    span: rustc_span::Span,
) -> Expr {
    use rustc_middle::ty;
    let kind = match c.kind() {
        ty::ConstKind::Param(p) => ExprKind::ConstRef { id: p.sinto(s) },
        ty::ConstKind::Infer(..) => span_fatal!(s, span, "ty::ConstKind::Infer node? {:#?}", c),
        ty::ConstKind::Unevaluated(..) => {
            span_fatal!(s, span, "ty::ConstKind::Unevaluated node? {:#?}", c)
        }
        ty::ConstKind::Value(valtree) => return valtree_to_expr(s, valtree, ty, span),
        ty::ConstKind::Error(valtree) => span_fatal!(s, span, "ty::ConstKind::Error"),
        ty::ConstKind::Expr(e) => {
            use rustc_middle::ty::Expr as CE;
            span_fatal!(s, span, "ty::ConstKind::Expr {:#?}", e)
        }
        kind => {
            supposely_unreachable!("const_to_expr": c, kind, span);
            span_fatal!(s, span, "const_to_expr, unexpected case")
        }
    };
    Decorated {
        ty: ty.sinto(s),
        span: span.sinto(s),
        contents: Box::new(kind),
        hir_id: None,
        attributes: vec![],
    }
}
#[tracing::instrument(skip(s))]
pub(crate) fn valtree_to_expr<'tcx, S: BaseState<'tcx>>(
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
        (ty::ValTree::Branch(valtrees), ty::Str) => ExprKind::Literal {
            lit: Spanned {
                node: LitKind::ByteStr(valtrees.into_iter().map(|x| match x {
                    ty::ValTree::Leaf(leaf) => leaf.try_to_u8().unwrap_or_else(|e| span_fatal!(s, span, "Expected a u8 leaf while translating a str literal, got something else. Error: {:#?}", e)),
                    _ => span_fatal!(s, span, "Expected a flat list of leaves while translating a str literal, got a arbitrary valtree.")
                }).collect(), StrStyle::Cooked),
                span: rustc_span::DUMMY_SP.sinto(s),
            },
            neg: false,
        },
        (ty::ValTree::Branch(_), ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) => {
            let contents: rustc_middle::ty::DestructuredConst = s
                .base().tcx
                .destructure_const(s.base().tcx.mk_const(valtree.clone(), ty));
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
                                value: const_to_expr(s, value, field.ty(s.base().tcx, substs), span),
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
                span: span.sinto(s),
            },
            neg: false,
        },
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

#[tracing::instrument(skip(s))]
pub(crate) fn get_variant_information<'s, S: BaseState<'s>>(
    adt_def: &rustc_middle::ty::AdtDef<'s>,
    variant: &rustc_hir::def_id::DefId,
    s: &S,
) -> VariantInformations {
    fn is_record<'s, I: std::iter::Iterator<Item = &'s rustc_middle::ty::FieldDef> + Clone>(
        it: I,
    ) -> bool {
        it.clone()
            .any(|field| !field.name.to_ident_string().parse::<u64>().is_ok())
    }
    let variant_def = adt_def
        .variants()
        .into_iter()
        .find(|v| v.def_id == variant.clone())
        .unwrap();
    let constructs_type = adt_def.did().sinto(s);
    VariantInformations {
        typ: constructs_type.clone(),
        variant: variant.sinto(s),

        typ_is_record: adt_def.is_struct() && is_record(adt_def.all_fields()),
        variant_is_record: is_record(variant_def.fields.iter()),
        typ_is_struct: adt_def.is_struct(),

        type_namespace: DefId {
            path: match constructs_type.path.as_slice() {
                [init @ .., _] => init.to_vec(),
                _ => {
                    let span = s.base().tcx.def_span(variant);
                    span_fatal!(
                        s,
                        span,
                        "Type {:#?} appears to have no path",
                        constructs_type
                    )
                }
            },
            ..constructs_type.clone()
        },
    }
}

#[tracing::instrument(skip(s))]
pub(crate) fn inspect_local_def_id<'tcx, S: BaseState<'tcx>>(
    did: rustc_hir::def_id::LocalDefId,
    owner_id: rustc_hir::hir_id::OwnerId,
    s: &S,
) -> (Rc<rustc_middle::thir::Thir<'tcx>>, Vec<Param>, Body) {
    let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
    let thirs = s.base().cached_thirs;

    let (thir, expr) = thirs
        .get(&did)
        .unwrap_or_else(|| span_fatal!(s, tcx.def_span(did), "Could not load body for id {did:?}"));

    let s = State {
        thir: thir.clone(),
        owner_id,
        base: s.base(),
    };
    let params: Vec<Param> = thir.params.iter().map(|x| x.sinto(&s)).collect();
    let body = expr.sinto(&s);
    (thir.clone(), params, body)
}

#[tracing::instrument]
pub(crate) fn read_span_from_file(span: &Span) -> Result<String, ReadSpanErr> {
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

#[tracing::instrument(skip(sess))]
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

#[tracing::instrument(skip(s))]
pub(crate) fn get_param_env<'tcx, S: BaseState<'tcx>>(s: &S) -> rustc_middle::ty::ParamEnv<'tcx> {
    match s.base().opt_def_id {
        Some(id) => s.base().tcx.param_env(id),
        None => rustc_middle::ty::ParamEnv::empty(),
    }
}

#[tracing::instrument(skip(s))]
pub(crate) fn _resolve_trait<'tcx, S: BaseState<'tcx>>(
    trait_ref: rustc_middle::ty::TraitRef<'tcx>,
    s: &S,
) {
    let tcx = s.base().tcx;
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
    // let id = s.base().opt_def_id.unwrap();
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

#[tracing::instrument]
pub fn argument_span_of_mac_call(mac_call: &rustc_ast::ast::MacCall) -> rustc_span::Span {
    (*mac_call.args).dspan.entire()
}
#[tracing::instrument(skip(state))]
pub(crate) fn raw_macro_invocation_of_span<'t, S: BaseState<'t>>(
    span: rustc_span::Span,
    state: &S,
) -> Option<(DefId, rustc_span::hygiene::ExpnData)> {
    let opts: Rc<hax_frontend_exporter_options::Options> = state.base().options;
    let macro_calls: crate::state::MacroCalls = state.base().macro_infos;

    let sess = state.base().tcx.sess;

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

#[tracing::instrument(skip(state))]
pub(crate) fn macro_invocation_of_raw_mac_invocation<'t, S: BaseState<'t>>(
    macro_ident: &DefId,
    expn_data: &rustc_span::hygiene::ExpnData,
    state: &S,
) -> MacroInvokation {
    let macro_infos = state.base().macro_infos;
    let mac_call_span = macro_infos
        .get(&translate_span(expn_data.call_site, state.base().tcx.sess))
        .unwrap_or_else(|| fatal!(state, "{:#?}", expn_data.call_site));
    MacroInvokation {
        macro_ident: macro_ident.clone(),
        argument: read_span_from_file(mac_call_span).unwrap(),
        span: expn_data.call_site.sinto(state),
    }
}

#[tracing::instrument(skip(state))]
pub(crate) fn macro_invocation_of_span<'t, S: BaseState<'t>>(
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

#[tracing::instrument(skip(s))]
pub(crate) fn attribute_from_scope<'tcx, S: ExprState<'tcx>>(
    s: &S,
    scope: &rustc_middle::middle::region::Scope,
) -> (Option<rustc_hir::hir_id::HirId>, Vec<Attribute>) {
    let owner = s.owner_id();
    let tcx = s.base().tcx;
    let scope_tree = tcx.region_scope_tree(owner.to_def_id());
    let hir_id = scope.hir_id(scope_tree);
    let tcx = s.base().tcx;
    let map = tcx.hir();
    let attributes = hir_id
        .map(|hir_id| map.attrs(hir_id).sinto(s))
        .unwrap_or(vec![]);
    (hir_id, attributes)
}

#[tracing::instrument(skip(s))]
pub(crate) fn make_fn_def<'tcx, S: BaseState<'tcx>>(
    fn_sig: &rustc_hir::FnSig,
    body_id: &rustc_hir::BodyId,
    s: &S,
) -> FnDef {
    let hir_id = body_id.hir_id;
    let (thir, params, body) =
        inspect_local_def_id(hir_id.clone().owner.def_id, hir_id.clone().owner, s);
    let ret = body.ty.clone();
    let s = State {
        thir: thir.clone(),
        base: s.base(),
        owner_id: (),
    };
    FnDef {
        params,
        ret,
        body,
        sig_span: fn_sig.span.sinto(&s),
        header: fn_sig.header.sinto(&s),
    }
}

use itertools::Itertools;

#[tracing::instrument(skip(s))]
pub fn inline_macro_invocations<'t, S: BaseState<'t>>(
    ids: &Vec<rustc_hir::ItemId>,
    s: &S,
) -> Vec<Item> {
    let tcx: rustc_middle::ty::TyCtxt = s.base().tcx;
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
        .group_by(|item| SpanEq(raw_macro_invocation_of_span(item.span, s)))
        .into_iter()
        .map(|(mac, items)| match mac.0 {
            Some((macro_ident, expn_data)) => {
                let owner_id = items.into_iter().map(|x| x.owner_id).next().unwrap();
                // owner_id.reduce()
                let invocation =
                    macro_invocation_of_raw_mac_invocation(&macro_ident, &expn_data, s);
                let span = expn_data.call_site.sinto(s);
                vec![Item {
                    def_id: None,
                    owner_id: owner_id.sinto(s),
                    // owner_id: expn_data.parent_module.unwrap().sinto(s),
                    kind: ItemKind::MacroInvokation(invocation),
                    span,
                    vis_span: rustc_span::DUMMY_SP.sinto(s),
                    attributes: vec![],
                    expn_backtrace: vec![],
                }]
            }
            _ => items.map(|item| item.sinto(s)).collect(),
        })
        .flatten()
        .collect()
}
