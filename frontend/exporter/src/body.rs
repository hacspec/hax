use crate::prelude::*;

pub use rustc_hir::{def_id::LocalDefId as RLocalDefId, hir_id::OwnerId as ROwnerId};

pub fn get_thir<'tcx, S: BaseState<'tcx>>(
    did: RLocalDefId,
    s: &S,
) -> (
    Rc<rustc_middle::thir::Thir<'tcx>>,
    rustc_middle::thir::ExprId,
) {
    let base = s.base();
    let msg = || span_fatal!(s, base.tcx.def_span(did), "THIR not found for {did:?}");
    base.cached_thirs.get(&did).unwrap_or_else(msg).clone()
}

pub trait IsBody: Sized + Clone {
    fn body<'tcx, S: BaseState<'tcx>>(did: RLocalDefId, owner: ROwnerId, s: &S) -> Self;
}

pub fn make_fn_def<'tcx, Body: IsBody, S: BaseState<'tcx>>(
    fn_sig: &rustc_hir::FnSig,
    body_id: &rustc_hir::BodyId,
    s: &S,
) -> FnDef<Body> {
    let hir_id = body_id.hir_id;
    let did = hir_id.clone().owner.def_id;
    let owner_id = hir_id.clone().owner;

    let (thir, expr_entrypoint) = get_thir(did, s);
    let s = &State {
        thir: thir.clone(),
        owner_id,
        base: s.base(),
        mir: (),
    };
    FnDef {
        params: thir.params.raw.sinto(s),
        ret: thir.exprs[expr_entrypoint].ty.sinto(s),
        body: Body::body(did, owner_id, s),
        sig_span: fn_sig.span.sinto(s),
        header: fn_sig.header.sinto(s),
    }
}

pub fn body_from_id<'tcx, Body: IsBody, S: BaseState<'tcx> + HasOwnerId>(
    id: rustc_hir::BodyId,
    s: &S,
) -> Body {
    Body::body(s.base().tcx.hir().body_owner_def_id(id), s.owner_id(), s)
}

mod implementations {
    use super::*;
    impl IsBody for () {
        fn body<'tcx, S: BaseState<'tcx>>(_did: RLocalDefId, _owner: ROwnerId, _s: &S) -> Self {
            ()
        }
    }
    impl IsBody for ThirBody {
        fn body<'tcx, S: BaseState<'tcx>>(did: RLocalDefId, owner_id: ROwnerId, s: &S) -> Self {
            let (thir, expr) = get_thir(did, s);
            expr.sinto(&State {
                thir,
                owner_id,
                base: s.base(),
                mir: (),
            })
        }
    }

    impl<A: IsBody, B: IsBody> IsBody for (A, B) {
        fn body<'tcx, S: BaseState<'tcx>>(did: RLocalDefId, owner_id: ROwnerId, s: &S) -> Self {
            (A::body(did, owner_id, s), B::body(did, owner_id, s))
        }
    }

    impl<MirKind: IsMirKind + Clone> IsBody for MirBody<MirKind> {
        fn body<'tcx, S: BaseState<'tcx>>(did: RLocalDefId, owner_id: ROwnerId, s: &S) -> Self {
            let (thir, _) = get_thir(did, s);
            let mir = Rc::new(s.base().tcx.mir_built(did).borrow().clone());
            mir.sinto(&State {
                thir,
                owner_id,
                base: s.base(),
                mir: mir.clone(),
            })
        }
    }
}

impl<'tcx, S: BaseState<'tcx> + HasOwnerId, Body: IsBody> SInto<S, Body> for rustc_hir::BodyId {
    fn sinto(&self, s: &S) -> Body {
        body_from_id::<Body, _>(self.clone(), s)
    }
}
