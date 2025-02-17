use hax_frontend_exporter::state::LocalContextS;
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
    hax_frontend_exporter::id_table::Table,
) {
    use hax_frontend_exporter::WithGlobalCacheExt;
    let mut state = hax_frontend_exporter::state::State::new(tcx, options.clone());
    state.base.macro_infos = Rc::new(macro_calls);

    let result = hax_frontend_exporter::inline_macro_invocations(tcx.hir().items(), &state);
    let impl_infos = hax_frontend_exporter::impl_def_ids_to_impled_types_and_bounds(&state)
        .into_iter()
        .collect();
    let exported_spans = state.with_global_cache(|cache| cache.spans.keys().copied().collect());
    let exported_def_ids = state.with_global_cache(|cache| {
        cache
            .per_item
            .values()
            .filter_map(|per_item_cache| per_item_cache.def_id.clone())
            .collect()
    });
    let cache_map = state.with_global_cache(|cache| cache.id_table_session.table().clone());

    (
        exported_spans,
        exported_def_ids,
        impl_infos,
        result,
        cache_map,
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
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_sess, providers| {
            hax_frontend_exporter::override_queries_store_body(providers);
        });
    }
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

            let output_dir = compiler.sess.io.output_dir.clone().unwrap();
            let haxmeta_path = output_dir.join(format!("{crate_name}-{cg_metadata}.haxmeta",));

            let mut file = BufWriter::new(File::create(&haxmeta_path).unwrap());

            use hax_types::driver_api::{with_kind_type, HaxMeta};
            with_kind_type!(
                self.body_types.clone(),
                <Body>|| {
                    let (spans, def_ids, impl_infos, items, cache_map) =
                        convert_thir(&self.clone().into(), self.macro_calls.clone(), tcx);
                    let files: HashSet<PathBuf> = HashSet::from_iter(
                        items
                            .iter()
                            .flat_map(|item| item.span.filename.to_path().map(|path| path.to_path_buf()))
                    );
                    let haxmeta: HaxMeta<Body> = HaxMeta {
                        crate_name,
                        cg_metadata,
                        externs,
                        impl_infos,
                        items,
                        comments: files.into_iter()
                            .flat_map(|path|hax_frontend_exporter::comments::comments_of_file(path).ok())
                            .flatten()
                            .collect(),
                        def_ids,
                        hax_version: hax_types::HAX_VERSION.into(),
                    };
                    haxmeta.write(&mut file, cache_map);
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
