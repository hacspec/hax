use hax_frontend_exporter;
use hax_frontend_exporter::state::{ExportedSpans, LocalContextS};
use hax_frontend_exporter::SInto;
use hax_types::cli_options::{Backend, PathOrDash, ENV_VAR_OPTIONS_FRONTEND};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::middle::region::Scope;
use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    thir,
    thir::{Block, BlockId, Expr, ExprId, ExprKind, Pat, PatKind, Stmt, StmtId, StmtKind, Thir},
};
use rustc_span::symbol::Symbol;
use serde::Serialize;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

type ThirBundle<'tcx> = (Rc<rustc_middle::thir::Thir<'tcx>>, ExprId);
/// Generates a dummy THIR body with an error literal as first expression
fn dummy_thir_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    span: rustc_span::Span,
    guar: rustc_errors::ErrorGuaranteed,
) -> ThirBundle<'tcx> {
    use rustc_middle::thir::*;
    let ty = tcx.mk_ty_from_kind(rustc_type_ir::TyKind::Never);
    let mut thir = Thir::new(BodyTy::Const(ty));
    let lit_err = tcx.hir_arena.alloc(rustc_span::source_map::Spanned {
        node: rustc_ast::ast::LitKind::Err(guar),
        span: rustc_span::DUMMY_SP,
    });
    let expr = thir.exprs.push(Expr {
        kind: ExprKind::Literal {
            lit: lit_err,
            neg: false,
        },
        ty,
        temp_lifetime: None,
        span,
    });
    (Rc::new(thir), expr)
}

/// Precompute all THIR bodies in a certain order so that we avoid
/// stealing issues (theoretically...)
fn precompute_local_thir_bodies<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> std::collections::HashMap<rustc_span::def_id::LocalDefId, ThirBundle<'tcx>> {
    let hir = tcx.hir();
    use rustc_hir::def::DefKind::*;
    use rustc_hir::*;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum ConstLevel {
        Const,
        ConstFn,
        NotConst,
    }

    #[tracing::instrument(skip(tcx))]
    fn const_level_of(tcx: TyCtxt<'_>, ldid: rustc_span::def_id::LocalDefId) -> ConstLevel {
        let did = ldid.to_def_id();
        if matches!(
            tcx.def_kind(did),
            Const | ConstParam | AssocConst | AnonConst | InlineConst
        ) {
            ConstLevel::Const
        } else if tcx.is_const_fn_raw(ldid.to_def_id()) {
            ConstLevel::ConstFn
        } else {
            ConstLevel::NotConst
        }
    }

    use itertools::Itertools;
    hir.body_owners()
        .filter(|ldid| {
            match tcx.def_kind(ldid.to_def_id()) {
                InlineConst | AnonConst => {
                    fn is_fn<'tcx>(tcx: TyCtxt<'tcx>, did: rustc_span::def_id::DefId) -> bool {
                        use rustc_hir::def::DefKind;
                        matches!(
                            tcx.def_kind(did),
                            DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(..) | DefKind::Closure
                        )
                    }
                    !is_fn(tcx, tcx.local_parent(*ldid).to_def_id())
                },
                _ => true
            }
        })
        .sorted_by_key(|ldid| const_level_of(tcx, *ldid))
        .filter(|ldid| hir.maybe_body_owned_by(*ldid).is_some())
        .map(|ldid| {
            tracing::debug!("⏳ Type-checking THIR body for {:#?}", ldid);
            let span = hir.span(tcx.local_def_id_to_hir_id(ldid));
            let (thir, expr) = match tcx.thir_body(ldid) {
                Ok(x) => x,
                Err(e) => {
                    let guar = tcx.dcx().span_err(
                        span,
                        "While trying to reach a body's THIR defintion, got a typechecking error.",
                    );
                    return (ldid, dummy_thir_body(tcx, span, guar));
                }
            };
            let thir = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                thir.borrow().clone()
            })) {
                Ok(x) => x,
                Err(e) => {
                    let guar = tcx.dcx().span_err(span, format!("The THIR body of item {:?} was stolen.\nThis is not supposed to happen.\nThis is a bug in Hax's frontend.\nThis is discussed in issue https://github.com/hacspec/hax/issues/27.\nPlease comment this issue if you see this error message!", ldid));
                    return (ldid, dummy_thir_body(tcx, span, guar));
                }
            };
            tracing::debug!("✅ Type-checked THIR body for {:#?}", ldid);
            (ldid, (Rc::new(thir), expr))
        })
        .collect()
}

/// Browse a crate and translate every item from HIR+THIR to "THIR'"
/// (I call "THIR'" the AST described in this crate)
#[tracing::instrument(skip_all)]
fn convert_thir<'tcx, Body: hax_frontend_exporter::IsBody>(
    options: &hax_frontend_exporter_options::Options,
    macro_calls: HashMap<hax_frontend_exporter::Span, hax_frontend_exporter::Span>,
    tcx: TyCtxt<'tcx>,
) -> (
    Vec<rustc_span::Span>,
    Vec<hax_frontend_exporter::DefId>,
    Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    Vec<hax_frontend_exporter::Item<Body>>,
) {
    let mut state = hax_frontend_exporter::state::State::new(tcx, options.clone());
    state.base.macro_infos = Rc::new(macro_calls);
    state.base.cached_thirs = Rc::new(precompute_local_thir_bodies(tcx));

    let result = hax_frontend_exporter::inline_macro_invocations(tcx.hir().items(), &state);
    let impl_infos = hax_frontend_exporter::impl_def_ids_to_impled_types_and_bounds(&state)
        .into_iter()
        .collect();
    let exported_spans = state.base.exported_spans.borrow().clone();

    let exported_def_ids = {
        let def_ids = state.base.exported_def_ids.borrow();
        let state = hax_frontend_exporter::state::State::new(tcx, options.clone());
        def_ids.iter().map(|did| did.sinto(&state)).collect()
    };
    (
        exported_spans.into_iter().collect(),
        exported_def_ids,
        impl_infos,
        result,
    )
}

/// Collect a map from spans to macro calls
#[tracing::instrument(skip_all)]
fn collect_macros(
    crate_ast: &rustc_ast::ast::Crate,
) -> HashMap<rustc_span::Span, rustc_ast::ast::MacCall> {
    use {rustc_ast::ast::*, rustc_ast::visit::*};
    struct MacroCollector {
        macro_calls: HashMap<rustc_span::Span, MacCall>,
    }
    impl<'ast> Visitor<'ast> for MacroCollector {
        fn visit_mac_call(&mut self, mac: &'ast rustc_ast::ast::MacCall) {
            self.macro_calls.insert(mac.span(), mac.clone());
        }
    }
    let mut v = MacroCollector {
        macro_calls: HashMap::new(),
    };
    v.visit_crate(crate_ast);
    v.macro_calls
}

/// Callback for extraction
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ExtractionCallbacks {
    pub inline_macro_calls: Vec<hax_types::cli_options::Namespace>,
    pub macro_calls: HashMap<hax_frontend_exporter::Span, hax_frontend_exporter::Span>,
    pub body_types: Vec<hax_types::cli_options::ExportBodyKind>,
}

impl From<ExtractionCallbacks> for hax_frontend_exporter_options::Options {
    fn from(opts: ExtractionCallbacks) -> hax_frontend_exporter_options::Options {
        hax_frontend_exporter_options::Options {
            inline_macro_calls: opts.inline_macro_calls,
        }
    }
}

impl Callbacks for ExtractionCallbacks {
    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let parse_ast = queries.parse().unwrap();
        let parse_ast = parse_ast.borrow();
        self.macro_calls = collect_macros(&parse_ast)
            .into_iter()
            .map(|(k, v)| {
                use hax_frontend_exporter::*;
                let sess = &compiler.sess;
                (
                    translate_span(k, sess),
                    translate_span(argument_span_of_mac_call(&v), sess),
                )
            })
            .collect();
        Compilation::Continue
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        use std::ops::{Deref, DerefMut};

        queries.global_ctxt().unwrap().enter(|tcx| {
            use hax_frontend_exporter::ThirBody;
            use hax_types::cli_options::Command;
            use rustc_session::config::CrateType;
            use serde::{Deserialize, Serialize};
            use std::fs::File;
            use std::io::BufWriter;

            use std::path::PathBuf;

            let opts = &compiler.sess.opts;
            let externs: Vec<_> = opts
                .externs
                .iter()
                .flat_map(|(_, ext)| match &ext.location {
                    rustc_session::config::ExternLocation::ExactPaths(set) => set
                        .iter()
                        .map(|cp| cp.canonicalized())
                        .collect::<Vec<_>>()
                        .into_iter(),
                    _ => vec![].into_iter(),
                })
                .map(|path| path.with_extension("haxmeta"))
                .collect();

            let cg_metadata = opts.cg.metadata[0].clone();
            let crate_name = opts.crate_name.clone().unwrap();
            let crate_type = match &opts.crate_types[..] {
                [crate_type] => format!("{}", crate_type),
                _ => panic!(),
            };

            let output_dir = compiler.sess.io.output_dir.clone().unwrap();
            let haxmeta_path =
                output_dir.join(format!("{crate_type}{crate_name}-{cg_metadata}.haxmeta",));

            let file = File::create(&haxmeta_path).unwrap();

            use hax_types::driver_api::{with_kind_type, HaxMeta};
            with_kind_type!(
                self.body_types.clone(),
                <Body>|| {
                    let (spans, def_ids, impl_infos, items) =
                        convert_thir(&self.clone().into(), self.macro_calls.clone(), tcx);
                    let haxmeta: HaxMeta<Body> = HaxMeta {
                        crate_name,
                        crate_type,
                        cg_metadata,
                        externs,
                        impl_infos,
                        items,
                        def_ids,
                    };
                    ciborium::into_writer(&haxmeta, BufWriter::new(file)).unwrap();
                }
            );

            let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let manifest_dir = std::path::Path::new(&manifest_dir);

            let data = hax_types::driver_api::EmitHaxMetaMessage {
                manifest_dir: manifest_dir.to_path_buf(),
                working_dir: opts
                    .working_dir
                    .to_path(rustc_span::FileNameDisplayPreference::Local)
                    .to_path_buf(),
                path: haxmeta_path,
            };
            eprintln!(
                "{}{}",
                hax_types::driver_api::HAX_DRIVER_STDERR_PREFIX,
                &serde_json::to_string(&hax_types::driver_api::HaxDriverMessage::EmitHaxMeta(data))
                    .unwrap()
            );

            Compilation::Stop
        })
    }
}
