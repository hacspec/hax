use hax_cli_options::{Backend, PathOrDash, ENV_VAR_OPTIONS_FRONTEND};
use hax_frontend_exporter;
use hax_frontend_exporter::state::{ExportedSpans, LocalContextS};
use hax_frontend_exporter::SInto;
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

fn report_diagnostics(
    output: &hax_cli_options_engine::Output,
    session: &rustc_session::Session,
    mapping: &Vec<(hax_frontend_exporter::Span, rustc_span::Span)>,
) {
    for d in &output.diagnostics {
        use hax_diagnostics::*;
        session.span_hax_err(d.convert(mapping).into());
    }
}

fn write_files(
    output: &hax_cli_options_engine::Output,
    session: &rustc_session::Session,
    backend: hax_cli_options::Backend,
) {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let manifest_dir = std::path::Path::new(&manifest_dir);
    let relative_path: std::path::PathBuf = ["proofs", format!("{backend}").as_str(), "extraction"]
        .iter()
        .collect();
    let out_dir = manifest_dir.join(&relative_path);
    for file in output.files.clone() {
        let path = out_dir.join(&file.path);
        std::fs::create_dir_all(&path.parent().unwrap()).unwrap();
        session.note_without_error(format!("Writing file {:#?}", path));
        std::fs::write(&path, file.contents).unwrap_or_else(|e| {
            session.fatal(format!(
                "Unable to write to file {:#?}. Error: {:#?}",
                path, e
            ))
        })
    }
}

type ThirBundle<'tcx> = (Rc<rustc_middle::thir::Thir<'tcx>>, ExprId);
/// Generates a dummy THIR body with an error literal as first expression
fn dummy_thir_body<'tcx>(tcx: TyCtxt<'tcx>, span: rustc_span::Span) -> ThirBundle<'tcx> {
    use rustc_middle::thir::*;
    let ty = tcx.mk_ty_from_kind(rustc_type_ir::sty::TyKind::Never);
    let mut thir = Thir::new(BodyTy::Const(ty));
    const ERR_LITERAL: &'static rustc_hir::Lit = &rustc_span::source_map::Spanned {
        node: rustc_ast::ast::LitKind::Err,
        span: rustc_span::DUMMY_SP,
    };
    let expr = thir.exprs.push(Expr {
        kind: ExprKind::Literal {
            lit: ERR_LITERAL,
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
            let span = hir.span(hir.local_def_id_to_hir_id(ldid));
            let (thir, expr) = match tcx.thir_body(ldid) {
                Ok(x) => x,
                Err(e) => {
                    tcx.sess.span_err(
                        span,
                        "While trying to reach a body's THIR defintion, got a typechecking error.",
                    );
                    return (ldid, dummy_thir_body(tcx, span));
                }
            };
            let thir = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                thir.borrow().clone()
            })) {
                Ok(x) => x,
                Err(e) => {
                    tcx.sess.span_err(span, format!("The THIR body of item {:?} was stolen.\nThis is not supposed to happen.\nThis is a bug in Hax's frontend.\nThis is discussed in issue https://github.com/hacspec/hax/issues/27.\nPlease comment this issue if you see this error message!", ldid));
                    return (ldid, dummy_thir_body(tcx, span));
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
    Vec<hax_frontend_exporter::Item<()>>,
) {
    let mut state = hax_frontend_exporter::state::State::new(tcx, options.clone());
    state.base.macro_infos = Rc::new(macro_calls);
    state.base.cached_thirs = Rc::new(precompute_local_thir_bodies(tcx));

    let mut exported_def_ids: HashSet<rustc_hir::def_id::DefId> = HashSet::new();

    // /// What should we do with the dependencies of a selected item?
    // enum DependentInclusion {
    //     Nothing,
    //     Signatures,
    //     Bodies,
    // }

    let mut with_bodies_queue: Vec<rustc_hir::ItemId> =
        tcx.hir().items().filter(|_| true).collect();
    // let mut without_bodies_queue: Vec<_> = vec![];
    for item_id in &with_bodies_queue {
        exported_def_ids.insert(item_id.owner_id.to_def_id());
    }

    let mut results = vec![];
    let mut signatures = vec![];

    while let Some(item_id) = with_bodies_queue.pop() {
        let item: hax_frontend_exporter::Item<Body> = item_id.sinto(&state);
        results.push(item);
        let mut state_exported_def_ids: HashSet<_> =
            state.base.exported_def_ids.borrow_mut().drain().collect();
        for def_id in state_exported_def_ids.drain() {
            if exported_def_ids.contains(&def_id) {
                continue;
            }
            exported_def_ids.insert(def_id);
            let item: hax_frontend_exporter::Item<()> = def_id.sinto(&state);
            signatures.push(item);
        }
    }

    let exported_spans = state.base.exported_spans.borrow().clone();
    *state.base.exported_def_ids.borrow_mut() = exported_def_ids;

    let exported_def_ids = {
        let def_ids = state.base.exported_def_ids.borrow();
        let state = hax_frontend_exporter::state::State::new(tcx, options.clone());
        def_ids.iter().map(|did| did.sinto(&state)).collect()
    };

    let impl_infos = hax_frontend_exporter::impl_def_ids_to_impled_types_and_bounds(&state)
        .into_iter()
        .collect();

    (
        exported_spans.into_iter().collect(),
        exported_def_ids,
        impl_infos,
        results,
        signatures,
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
        .unwrap_or_else(|| {
            fn is_opam_setup_correctly() -> bool {
                std::env::var("OPAM_SWITCH_PREFIX").is_ok()
            }
            use colored::Colorize;
            eprintln!("\n{}\n{}\n\n{} {}\n",
                      &ENGINE_BINARY_NOT_FOUND,
                      "Please make sure the engine is installed and is in PATH!",
                      "Hint: With OPAM, `eval $(opam env)` is necessary for OPAM binaries to be in PATH: make sure to run `eval $(opam env)` before running `cargo hax`.".bright_black(),
                      format!("(diagnostics: {})", if is_opam_setup_correctly() { "opam seems okay ✓" } else {"opam seems not okay ❌"}).bright_black()
            );
            panic!("{}", &ENGINE_BINARY_NOT_FOUND)
        })
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
            use hax_cli_options::ExporterCommand;
            match self.command.clone() {
                ExporterCommand::JSON {
                    output_file,
                    mut kind,
                    include_extra,
                } => {
                    struct Driver<'tcx> {
                        options: hax_frontend_exporter_options::Options,
                        macro_calls:
                            HashMap<hax_frontend_exporter::Span, hax_frontend_exporter::Span>,
                        tcx: TyCtxt<'tcx>,
                        output_file: PathOrDash,
                        include_extra: bool,
                    }
                    impl<'tcx> Driver<'tcx> {
                        fn to_json<Body: hax_frontend_exporter::IsBody + Serialize>(self) {
                            let (_, def_ids, impl_infos, converted_items, signatures) =
                                convert_thir::<Body>(
                                    &self.options,
                                    self.macro_calls.clone(),
                                    self.tcx,
                                );

                            let dest = self.output_file.open_or_stdout();
                            (if self.include_extra {
                                serde_json::to_writer(
                                    dest,
                                    &hax_cli_options_engine::WithDefIds {
                                        def_ids,
                                        impl_infos,
                                        items: converted_items,
                                    },
                                )
                            } else {
                                serde_json::to_writer(dest, &(converted_items, signatures))
                            })
                            .unwrap()
                        }
                    }
                    let driver = Driver {
                        options: self.clone().into(),
                        macro_calls: self.macro_calls.clone(),
                        tcx,
                        output_file,
                        include_extra,
                    };
                    mod from {
                        pub use hax_cli_options::ExportBodyKind::{
                            MirBuilt as MB, MirConst as MC, Thir as T,
                        };
                    }
                    mod to {
                        pub type T = hax_frontend_exporter::ThirBody;
                        pub type MB =
                            hax_frontend_exporter::MirBody<hax_frontend_exporter::mir_kinds::Built>;
                        pub type MC =
                            hax_frontend_exporter::MirBody<hax_frontend_exporter::mir_kinds::Const>;
                    }
                    kind.sort();
                    kind.dedup();
                    match kind.as_slice() {
                        [from::MB] => driver.to_json::<to::MB>(),
                        [from::MC] => driver.to_json::<to::MC>(),
                        [from::T] => driver.to_json::<to::T>(),
                        [from::MB, from::MC] => driver.to_json::<(to::MB, to::MC)>(),
                        [from::T, from::MB] => driver.to_json::<(to::MB, to::T)>(),
                        [from::T, from::MC] => driver.to_json::<(to::MC, to::T)>(),
                        [from::T, from::MB, from::MC] => {
                            driver.to_json::<(to::MB, (to::MC, to::T))>()
                        }
                        [] => driver.to_json::<()>(),
                        _ => panic!("Unsupported kind {:#?}", kind),
                    }
                }
                ExporterCommand::Backend(backend) => {
                    if matches!(backend.backend, Backend::Easycrypt | Backend::ProVerif(..)) {
                        eprintln!(
                            "⚠️ Warning: Experimental backend \"{}\" is work in progress.",
                            backend.backend
                        )
                    }

                    let (spans, _def_ids, impl_infos, converted_items, _) =
                        convert_thir(&self.clone().into(), self.macro_calls.clone(), tcx);

                    let engine_options = hax_cli_options_engine::EngineOptions {
                        backend: backend.clone(),
                        input: converted_items,
                        impl_infos,
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

                    serde_json::to_writer::<_, hax_cli_options_engine::EngineOptions>(
                        std::io::BufWriter::new(
                            engine_subprocess
                                .stdin
                                .as_mut()
                                .expect("Could not write on stdin"),
                        ),
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
                    let options_frontend =
                        hax_frontend_exporter_options::Options::from(self.clone());
                    let state =
                        hax_frontend_exporter::state::State::new(tcx, options_frontend.clone());
                    report_diagnostics(
                        &output,
                        &session,
                        &spans
                            .into_iter()
                            .map(|span| (span.sinto(&state), span.clone()))
                            .collect(),
                    );
                    if backend.dry_run {
                        serde_json::to_writer(std::io::BufWriter::new(std::io::stdout()), &output)
                            .unwrap()
                    } else {
                        write_files(&output, &session, backend.backend);
                    }
                    if let Some(debug_json) = &output.debug_json {
                        use hax_cli_options::DebugEngineMode;
                        match backend.debug_engine {
                            Some(DebugEngineMode::Interactive) => {
                                eprintln!("----------------------------------------------");
                                eprintln!("----------------------------------------------");
                                eprintln!("----------------------------------------------");
                                eprintln!("-- Engine debug mode. Press CTRL+C to exit. --");
                                eprintln!("----------------------------------------------");
                                eprintln!("----------------------------------------------");
                                eprintln!("----------------------------------------------");
                                hax_phase_debug_webapp::run(|| debug_json.clone())
                            }
                            Some(DebugEngineMode::File(file)) if !backend.dry_run => {
                                println!("{}", debug_json)
                            }
                            _ => (),
                        }
                    }
                }
            };
            Compilation::Stop
        })
    }
}
