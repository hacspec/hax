pub use module::*;

#[cfg(not(feature = "rustc"))]
mod module {
    pub trait IsBody: Sized + Clone + 'static {}
    impl<T: Sized + Clone + 'static> IsBody for T {}
}

#[cfg(feature = "rustc")]
mod module {
    pub use crate::prelude::*;
    pub use rustc_hir::{
        def_id::{DefId as RDefId, LocalDefId as RLocalDefId},
        hir_id::OwnerId as ROwnerId,
    };

    mod store {
        //! This module helps at store bodies to avoid stealing.
        //! `rustc_data_structures::steal::Steal` is a box for which the content can be stolen, for performance reasons.
        //! The query system of Rust creates and steal such boxes, resulting in hax trying to borrow the value of a Steal while some query stole it already.
        //! This module provides an ad-hoc global cache and query overrides to deal with this issue.
        use rustc_hir::def_id::LocalDefId;
        use rustc_middle::mir::Body;
        use rustc_middle::query::plumbing::IntoQueryParam;
        use rustc_middle::thir::{ExprId, Thir};
        use std::cell::RefCell;
        use std::collections::HashMap;
        use std::rc::Rc;

        thread_local! {
            static THIR_BODY: RefCell<HashMap<LocalDefId, (Rc<Thir<'static>>, ExprId)>> = RefCell::new(HashMap::new());
            static MIR_BUILT: RefCell<HashMap<LocalDefId, Rc<Body<'static>>>> = RefCell::new(HashMap::new());
        }

        /// Register overrides for rustc queries.
        /// This will clone and store bodies for THIR and MIR (built) in an ad-hoc global cache.
        pub fn override_queries_store_body(providers: &mut rustc_middle::query::Providers) {
            providers.thir_body = |tcx, def_id| {
                let (steal, expr_id) =
                    (rustc_interface::DEFAULT_QUERY_PROVIDERS.thir_body)(tcx, def_id)?;
                let body = steal.borrow().clone();
                let body: Thir<'static> = unsafe { std::mem::transmute(body) };
                THIR_BODY.with(|map| map.borrow_mut().insert(def_id, (Rc::new(body), expr_id)));
                Ok((steal, expr_id))
            };
            providers.mir_built = |tcx, def_id| {
                let steal = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let body = steal.borrow().clone();
                let body: Body<'static> = unsafe { std::mem::transmute(body) };
                MIR_BUILT.with(|map| map.borrow_mut().insert(def_id, Rc::new(body)));
                steal
            };
        }

        /// Extension trait that provides non-stealing variants of `thir_body` and `mir_built`.
        /// Those methods requires rustc queries to be overriden with the helper function `register` above.
        #[extension_traits::extension(pub trait SafeTyCtxtBodies)]
        impl<'tcx> rustc_middle::ty::TyCtxt<'tcx> {
            fn thir_body_safe(
                &self,
                key: impl IntoQueryParam<rustc_span::def_id::LocalDefId>,
            ) -> Result<(Rc<Thir<'tcx>>, ExprId), rustc_span::ErrorGuaranteed> {
                let key = key.into_query_param();
                if !THIR_BODY.with(|map| map.borrow().contains_key(&key)) {
                    // Compute a body, which will insert a body in `THIR_BODIES`.
                    let _ = self.thir_body(key);
                }
                THIR_BODY.with(|map| {
                    let (body, expr) = map
                        .borrow_mut()
                        .get(&key)
                        .expect("Did we forgot to call `register`?")
                        .clone();
                    let body: Rc<Thir<'tcx>> = unsafe { std::mem::transmute(body) };
                    Ok((body, expr))
                })
            }
            fn mir_built_safe(
                &self,
                key: impl IntoQueryParam<rustc_span::def_id::LocalDefId>,
            ) -> Rc<Body<'tcx>> {
                let key = key.into_query_param();
                if !MIR_BUILT.with(|map| map.borrow().contains_key(&key)) {
                    // Compute a body, which will insert a body in `MIR_BODIES`.
                    let _ = self.mir_built(key);
                }
                MIR_BUILT.with(|map| {
                    let body = map
                        .borrow_mut()
                        .get(&key)
                        .expect("Did we forgot to call `register`?")
                        .clone();
                    unsafe { std::mem::transmute(body) }
                })
            }
        }
    }
    pub use store::*;

    pub fn get_thir<'tcx, S: UnderOwnerState<'tcx>>(
        did: RLocalDefId,
        s: &S,
    ) -> (
        Rc<rustc_middle::thir::Thir<'tcx>>,
        rustc_middle::thir::ExprId,
    ) {
        let tcx = s.base().tcx;
        s.with_item_cache(did.to_def_id(), |caches| {
            let msg = || fatal!(s[tcx.def_span(did)], "THIR not found for {:?}", did);
            caches.thir.as_ref().unwrap_or_else(msg).clone()
        })
    }

    pub trait IsBody: Sized + Clone + 'static {
        fn body<'tcx, S: UnderOwnerState<'tcx>>(did: RLocalDefId, s: &S) -> Self;
    }

    pub fn make_fn_def<'tcx, Body: IsBody, S: UnderOwnerState<'tcx>>(
        fn_sig: &rustc_hir::FnSig,
        body_id: &rustc_hir::BodyId,
        s: &S,
    ) -> FnDef<Body> {
        let hir_id = body_id.hir_id;
        let ldid = hir_id.owner.def_id;

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
        // **Important:**
        // We need a local id here, and we get it from the owner id, which must
        // be local. It is safe to do so, because if we have access to HIR objects,
        // it necessarily means we are exploring a local item (we don't have
        // access to the HIR of external objects, only their MIR).
        Body::body(s.base().tcx.hir().body_owner_def_id(id), s)
    }

    mod implementations {
        use super::*;
        impl IsBody for () {
            fn body<'tcx, S: UnderOwnerState<'tcx>>(_did: RLocalDefId, _s: &S) -> Self {}
        }
        impl IsBody for ThirBody {
            fn body<'tcx, S: UnderOwnerState<'tcx>>(did: RLocalDefId, s: &S) -> Self {
                let (thir, expr) = get_thir(did, s);
                if *CORE_EXTRACTION_MODE {
                    let expr = &thir.exprs[expr];
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

        impl<MirKind: IsMirKind + Clone + 'static> IsBody for MirBody<MirKind> {
            fn body<'tcx, S: UnderOwnerState<'tcx>>(did: RLocalDefId, s: &S) -> Self {
                let (thir, _) = get_thir(did, s);
                let mir = MirKind::get_mir(s.base().tcx, did, |body| {
                    let body = Rc::new(body.clone());
                    body.sinto(&with_owner_id(
                        s.base(),
                        thir,
                        body.clone(),
                        did.to_def_id(),
                    ))
                });
                mir.s_unwrap(s)
            }
        }
    }

    impl<'tcx, S: UnderOwnerState<'tcx>, Body: IsBody> SInto<S, Body> for rustc_hir::BodyId {
        fn sinto(&self, s: &S) -> Body {
            body_from_id::<Body, _>(*self, s)
        }
    }
}
