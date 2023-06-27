use hax_cli_options::{PathOrDash, ENV_VAR_OPTIONS_FRONTEND};
use hax_frontend_exporter;
use hax_frontend_exporter::types::{ExportedSpans, LocalContextS};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::middle::region::Scope;
use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    thir,
    thir::{Block, BlockId, Expr, ExprId, ExprKind, Pat, PatKind, Stmt, StmtId, StmtKind, Thir},
};
use rustc_session::parse::ParseSess;
use rustc_span::symbol::Symbol;
use serde::Serialize;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Browse a crate and translate every item from HIR+THIR to "THIR'"
/// (I call "THIR'" the AST described in this crate)
fn convert_thir<'tcx>(
    options: &hax_frontend_exporter_options::Options,
    macro_calls: HashMap<hax_frontend_exporter::Span, hax_frontend_exporter::Span>,
    tcx: TyCtxt<'tcx>,
) -> (Vec<rustc_span::Span>, Vec<hax_frontend_exporter::Item>) {
    let hir = tcx.hir();

    let bodies = {
        // Here, we partition the bodies so that constant items appear
        // first.
        let (consts, others): (Vec<rustc_span::def_id::LocalDefId>, _) = hir
            .body_owners()
            .partition(|x: &rustc_span::def_id::LocalDefId| {
                matches!(
                    hir.get_by_def_id(x.clone()),
                    rustc_hir::Node::AnonConst(_)
                        | rustc_hir::Node::Item(rustc_hir::Item {
                            kind: rustc_hir::ItemKind::Const(..),
                            ..
                        })
                        | rustc_hir::Node::TraitItem(rustc_hir::TraitItem {
                            kind: rustc_hir::TraitItemKind::Const(..),
                            ..
                        })
                        | rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
                            kind: rustc_hir::ImplItemKind::Const(..),
                            ..
                        })
                )
            });
        consts.into_iter().chain(others.into_iter())
    };

    let thirs: std::collections::HashMap<
        rustc_span::def_id::LocalDefId,
        (rustc_middle::thir::Thir<'tcx>, ExprId),
    > = bodies
        .map(|did| {
            let span = hir.span(hir.local_def_id_to_hir_id(did));
            let mk_error_thir = || {
                let ty = tcx.mk_ty_from_kind(rustc_type_ir::sty::TyKind::Never);
                let mut thir = rustc_middle::thir::Thir::new(rustc_middle::thir::BodyTy::Const(ty));
                const ERR_LITERAL: &'static rustc_hir::Lit = &rustc_span::source_map::Spanned {
                    node: rustc_ast::ast::LitKind::Err,
                    span: rustc_span::DUMMY_SP,
                };
                let expr = thir.exprs.push(rustc_middle::thir::Expr {
                    kind: rustc_middle::thir::ExprKind::Literal {
                        lit: ERR_LITERAL,
                        neg: false,
                    },
                    ty,
                    temp_lifetime: None,
                    span,
                });
                (did, (thir, expr))
            };
            let (thir, expr) = match tcx.thir_body(did) {
                Ok(x) => x,
                Err(e) => {
                    tcx.sess.span_err(
                        span,
                        "While trying to reach a body's THIR defintion, got a typechecking error.",
                    );
                    return mk_error_thir();
                }
            };
            let thir = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                // Borrowing `Thir` from a `Steal`!
                thir.borrow().clone()
            })) {
                Ok(x) => x,
                Err(e) => {
                    let message = format!("The THIR body of item {:?} was stolen.\nThis is not supposed to happen.\nThis is a bug in Hax's frontend.\nThis is discussed in issue https://github.com/hacspec/hacspec-v2/issues/27.\nPlease comment this issue if you see this error message!", did);
                    tcx.sess.span_err(span, message);
                    return mk_error_thir();
                }
            };
            (did, (thir, expr))
        })
        .collect();

    let items = hir.items();
    let macro_calls_r = Box::new(macro_calls);
    let state = hax_frontend_exporter::State {
        tcx,
        options: Box::new(options.clone()),
        thir: (),
        owner_id: (),
        opt_def_id: None,
        macro_infos: macro_calls_r,
        local_ctx: Rc::new(RefCell::new(LocalContextS::new())),
        cached_thirs: thirs,
        exported_spans: Rc::new(RefCell::new(HashSet::new())),
    };

    let result = hax_frontend_exporter::inline_macro_invocations(&items.collect(), &state);
    let exported_spans = state.exported_spans.borrow().clone();
    (exported_spans.into_iter().collect(), result)
}

/// Collect a map from spans to macro calls
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

const ENGINE_BINARY_NAME: &str = "hax-engine";
const ENGINE_BINARY_NOT_FOUND: &str = const_format::formatcp!(
    "The binary [{}] was not found in your [PATH].",
    ENGINE_BINARY_NAME,
);

/// Dynamically looks for binary [ENGINE_BINARY_NAME].  First, we
/// check whether [HAX_ENGINE_BINARY] is set, and use that if it
/// is. Then, we try to find [ENGINE_BINARY_NAME] in PATH. If not
/// found, detect whether nodejs is available, download the JS-compiled
/// engine and use it.
use std::process;
fn find_hax_engine() -> process::Command {
    use which::which;

    std::env::var("HAX_ENGINE_BINARY")
        .ok()
        .map(|name| process::Command::new(name))
        .or_else(|| {
            which(ENGINE_BINARY_NAME)
                .ok()
                .map(|name| process::Command::new(name))
        })
        .or_else(|| {
            which("node").ok().and_then(|_| {
                if let Ok(true) = inquire::Confirm::new(&format!(
                    "{} Should I try to download it from GitHub?",
                    ENGINE_BINARY_NOT_FOUND,
                ))
                .with_default(true)
                .prompt()
                {
                    let cmd = process::Command::new("node");
                    let engine_js_path: String =
                        panic!("TODO: Downloading from GitHub is not supported yet.");
                    cmd.arg(engine_js_path);
                    Some(cmd)
                } else {
                    None
                }
            })
        })
        .expect(&ENGINE_BINARY_NOT_FOUND)
}

/// Callback for extraction
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ExtractionCallbacks {
    pub inline_macro_calls: Vec<hax_cli_options::Namespace>,
    pub command: hax_cli_options::ExporterCommand,
    pub macro_calls: HashMap<hax_frontend_exporter::Span, hax_frontend_exporter::Span>,
}

impl From<ExtractionCallbacks> for hax_frontend_exporter_options::Options {
    fn from(opts: ExtractionCallbacks) -> hax_frontend_exporter_options::Options {
        hax_frontend_exporter_options::Options {
            inline_macro_calls: opts.inline_macro_calls,
        }
    }
}

impl Callbacks for ExtractionCallbacks {
    fn after_parsing<'tcx>(
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
                let sess = compiler.session();
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
            let (spans, converted_items) =
                convert_thir(&self.clone().into(), self.macro_calls.clone(), tcx);

            use hax_cli_options::ExporterCommand;
            match self.command.clone() {
                ExporterCommand::JSON { output_file } => {
                    serde_json::to_writer_pretty(output_file.open_or_stdout(), &converted_items)
                        .unwrap()
                }
                ExporterCommand::Backend(backend) => {
                    let engine_options = hax_cli_options_engine::EngineOptions {
                        backend: backend.clone(),
                        input: converted_items,
                    };
                    let mut engine_subprocess = find_hax_engine()
                        .stdin(std::process::Stdio::piped())
                        .stdout(std::process::Stdio::piped())
                        .spawn()
                        .map_err(|e| {
                            if let std::io::ErrorKind::NotFound = e.kind() {
                                panic!(
                                    "The binary [{}] was not found in your [PATH].",
                                    ENGINE_BINARY_NAME
                                )
                            }
                            e
                        })
                        .unwrap();

                    serde_json::to_writer(
                        engine_subprocess
                            .stdin
                            .as_mut()
                            .expect("Could not write on stdin"),
                        &engine_options,
                    )
                    .unwrap();

                    let out = engine_subprocess.wait_with_output().unwrap();
                    let session = compiler.session();
                    if !out.status.success() {
                        session.fatal(format!(
                            "{} exited with non-zero code {}\nstdout: {}\n stderr: {}",
                            ENGINE_BINARY_NAME,
                            out.status.code().unwrap_or(-1),
                            String::from_utf8(out.stdout).unwrap(),
                            String::from_utf8(out.stderr).unwrap(),
                        ));
                        return Compilation::Stop;
                    }
                    let output: hax_cli_options_engine::Output =
                        serde_json::from_slice(out.stdout.as_slice()).unwrap_or_else(|_| {
                            panic!(
                                "{} outputed incorrect JSON {}",
                                ENGINE_BINARY_NAME,
                                String::from_utf8(out.stdout).unwrap()
                            )
                        });
                    let options_frontend = Box::new(
                        hax_frontend_exporter_options::Options::from(self.clone()).clone(),
                    );
                    let state = hax_frontend_exporter::State {
                        tcx,
                        options: options_frontend,
                        thir: (),
                        owner_id: (),
                        opt_def_id: None::<rustc_hir::def_id::DefId>,
                        macro_infos: Box::new(HashMap::new()),
                        local_ctx: Rc::new(RefCell::new(LocalContextS::new())),
                        cached_thirs: HashMap::new(),
                        exported_spans: Rc::new(RefCell::new(HashSet::new())),
                    };
                    for d in output.diagnostics {
                        use hax_diagnostics::*;
                        use hax_frontend_exporter::SInto;
                        let mut relevant_spans: Vec<_> = spans
                            .iter()
                            .filter(|span| span.sinto(&state) == d.span)
                            .cloned()
                            .collect();
                        relevant_spans.sort();
                        session.span_hax_err(
                            d.set_span(
                                relevant_spans
                                    .first()
                                    .cloned()
                                    .unwrap_or(rustc_span::DUMMY_SP),
                            ),
                        );
                    }
                    let metadata = cargo_metadata::MetadataCommand::new().exec().unwrap();
                    let crate_name = std::env::var("CARGO_CRATE_NAME").unwrap();
                    let package = metadata
                        .packages
                        .iter()
                        .rfind(|pkg| pkg.name == crate_name)
                        .unwrap();
                    let manifest_path = package.manifest_path.clone();
                    let relative_path: cargo_metadata::camino::Utf8PathBuf =
                        ["hax", format!("{}", backend.backend).as_str(), "extraction"]
                            .iter()
                            .collect();
                    let output_dir = manifest_path.parent().unwrap().join(relative_path);
                    for file in output.files.clone() {
                        let path = output_dir.join(file.path);
                        std::fs::create_dir_all({
                            let mut parent = path.clone();
                            parent.pop();
                            parent
                        })
                        .unwrap();
                        session.note_without_error(format!("Writing file {:#?}", path));
                        std::fs::write(&path, file.contents).unwrap_or_else(|e| {
                            session.fatal(format!(
                                "Unable to write to file {:#?}. Error: {:#?}",
                                path, e
                            ))
                        })
                    }
                }
            };
            Compilation::Continue
        })
    }
}
