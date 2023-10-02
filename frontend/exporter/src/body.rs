use crate::prelude::*;

pub use rustc_hir::{
    def_id::{DefId as RDefId, LocalDefId as RLocalDefId},
    hir_id::OwnerId as ROwnerId,
};

pub fn get_thir<'tcx, S: UnderOwnerState<'tcx>>(
    did: RLocalDefId,
    s: &S,
) -> (
    Rc<rustc_middle::thir::Thir<'tcx>>,
    rustc_middle::thir::ExprId,
) {
    let base = s.base();
    let msg = || fatal!(s[base.tcx.def_span(did)], "THIR not found for {:?}", did);
    base.cached_thirs.get(&did).unwrap_or_else(msg).clone()
}

pub trait IsBody: Sized + Clone {
    fn body<'tcx, S: UnderOwnerState<'tcx>>(did: RLocalDefId, s: &S) -> Self;
}

pub fn make_fn_def<'tcx, Body: IsBody, S: UnderOwnerState<'tcx>>(
    fn_sig: &rustc_hir::FnSig,
    body_id: &rustc_hir::BodyId,
    s: &S,
) -> FnDef<Body> {
    let hir_id = body_id.hir_id;
    let ldid = hir_id.clone().owner.def_id;

    let (thir, expr_entrypoint) = get_thir(ldid, s);
    let s = &with_owner_id(s.base(), thir.clone(), (), ldid.to_def_id());
    FnDef {
        params: thir.params.raw.sinto(s),
        ret: thir.exprs[expr_entrypoint].ty.sinto(s),
        body: Body::body(ldid, s),
        sig_span: fn_sig.span.sinto(s),
        header: fn_sig.header.sinto(s),
    }
}

pub fn body_from_id<'tcx, Body: IsBody, S: UnderOwnerState<'tcx>>(
    id: rustc_hir::BodyId,
    s: &S,
) -> Body {
    Body::body(s.base().tcx.hir().body_owner_def_id(id), s)
}

mod implementations {
    use super::*;
    impl IsBody for () {
        fn body<'tcx, S: UnderOwnerState<'tcx>>(_did: RLocalDefId, _s: &S) -> Self {
            ()
        }
    }
    impl IsBody for ThirBody {
        fn body<'tcx, S: UnderOwnerState<'tcx>>(did: RLocalDefId, s: &S) -> Self {
            let (thir, expr) = get_thir(did, s);
            if *CORE_EXTRACTION_MODE {
                let expr = &thir.exprs[expr.clone()];
                Decorated {
                    contents: Box::new(ExprKind::Tuple { fields: vec![] }),
                    hir_id: None,
                    attributes: vec![],
                    ty: expr.ty.sinto(s),
                    span: expr.span.sinto(s),
                }
            } else {
                expr.sinto(&with_owner_id(s.base(), thir, (), did.to_def_id()))
            }
        }
    }

    impl<A: IsBody, B: IsBody> IsBody for (A, B) {
        fn body<'tcx, S: UnderOwnerState<'tcx>>(did: RLocalDefId, s: &S) -> Self {
            (A::body(did, s), B::body(did, s))
        }
    }

    impl<MirKind: IsMirKind + Clone> IsBody for MirBody<MirKind> {
        fn body<'tcx, S: UnderOwnerState<'tcx>>(did: RLocalDefId, s: &S) -> Self {
            let (thir, _) = get_thir(did, s);
            let mir = Rc::new(s.base().tcx.mir_built(did).borrow().clone());
            mir.sinto(&with_owner_id(s.base(), thir, mir.clone(), did.to_def_id()))
        }
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>, Body: IsBody> SInto<S, Body> for rustc_hir::BodyId {
    fn sinto(&self, s: &S) -> Body {
        body_from_id::<Body, _>(self.clone(), s)
    }
}
