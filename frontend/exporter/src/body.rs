use crate::prelude::*;

pub use rustc_hir::{def_id::LocalDefId as RLocalDefId, hir_id::OwnerId as ROwnerId};

pub trait RequiredTraits = JsonSchema + Clone + serde::Serialize + core::fmt::Debug;

pub trait IsOptions: RequiredTraits {
    type Body<O: IsOptions>: IsBody + RequiredTraits;
    type Const<O: IsOptions>: IsConst + RequiredTraits;
    // type DefId: IsDefId + RequiredTraits;
}

impl<O: IsOptions> IsConst for Box<Expr<O>> {
    fn of_ty_const<'tcx, S: BaseState<'tcx>>(c: &rustc_middle::ty::Const<'tcx>, s: &S) -> Self {
        panic!()
    }
    fn of_mir_constant_kind<'tcx, S: BaseState<'tcx>>(
        c: &rustc_middle::mir::ConstantKind<'tcx>,
        s: &S,
    ) -> Self {
        panic!()
    }
}

pub mod options {
    use super::*;
    use std::marker::PhantomData;
    #[derive(Debug, Clone, Copy, Serialize, JsonSchema)]
    pub struct Thir;
    impl IsOptions for Thir {
        type Body<O: IsOptions> = Expr<O>;
        type Const<O: IsOptions> = Box<Expr<O>>;
    }

    // #[derive(Debug, Clone, Copy)]
    // pub struct Opts<Body: IsBody + RequiredTraits, Const: IsConst + RequiredTraits> {
    //     _body: PhantomData<Body>,
    //     _const: PhantomData<Const>,
    // }

    // impl<Body: IsBody + RequiredTraits, Const: IsConst + RequiredTraits> Opts<Body, Const> {
    //     pub fn new() -> Opts<Body, Const> {
    //         Opts {
    //             _body: PhantomData,
    //             _const: PhantomData,
    //         }
    //     }
    // }

    // impl<Body: IsBody + RequiredTraits, Const: IsConst + RequiredTraits> IsOptions
    //     for Opts<Body, Const>
    // {
    //     type Body = Body;
    //     type Const = Const;
    // }
}

// pub trait IsDefId {
//     fn of_def_id<'tcx, S: BaseState<'tcx>>(c: rustc_hir::def_id::DefId, s: &S) -> Self;
// }

pub trait IsConst {
    fn of_ty_const<'tcx, S: BaseState<'tcx>>(c: &rustc_middle::ty::Const<'tcx>, s: &S) -> Self;
    fn of_mir_constant_kind<'tcx, S: BaseState<'tcx>>(
        c: &rustc_middle::mir::ConstantKind<'tcx>,
        s: &S,
    ) -> Self;
}

impl<'tcx, S: BaseState<'tcx>, C: IsConst> SInto<S, C> for rustc_middle::mir::ConstantKind<'tcx> {
    fn sinto(&self, s: &S) -> C {
        C::of_mir_constant_kind(self, s)
    }
}

impl<'tcx, S: BaseState<'tcx>, C: IsConst> SInto<S, C> for rustc_middle::ty::Const<'tcx> {
    fn sinto(&self, s: &S) -> C {
        C::of_ty_const(self, s)
    }
}

// impl<'tcx, S: BaseState<'tcx>, DID: IsDefId> SInto<S, DID> for rustc_span::def_id::DefId {
//     fn sinto(&self, s: &S) -> DID {
//         DID::of_def_id(*self, s)
//     }
// }

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

pub fn make_fn_def<'tcx, O: IsOptions, S: BaseState<'tcx>>(
    fn_sig: &rustc_hir::FnSig,
    body_id: &rustc_hir::BodyId,
    s: &S,
) -> FnDef<O> {
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
        body: O::Body::body(did, owner_id, s),
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
    impl<O: IsOptions> IsBody for ThirBody<O> {
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

    impl<MirKind: IsMirKind + Clone, O: IsOptions> IsBody for MirBody<O, MirKind> {
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
