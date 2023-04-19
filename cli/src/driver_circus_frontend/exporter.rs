use circus_cli_options::ENV_VAR_OPTIONS_FRONTEND;
use circus_frontend_exporter;
use circus_frontend_exporter::types::ExportedSpans;
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
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

fn convert_thir<'tcx>(
    options: &circus_frontend_exporter::options::Options,
    macro_calls: HashMap<rustc_span::Span, rustc_ast::ast::MacCall>,
    tcx: TyCtxt<'tcx>,
) -> (Vec<rustc_span::Span>, Vec<circus_frontend_exporter::Item>) {
    let hir = tcx.hir();
    let bodies = hir.body_owners();

    let mut bodies = bodies.collect::<Vec<_>>();
    // we first visit `AnonConst`s, otherwise the thir body might be stolen
    bodies.sort_by(|a, b| {
        use std::cmp::Ordering::*;
        let is_anon_const = |x: &rustc_span::def_id::LocalDefId| {
            matches!(hir.get_by_def_id(x.clone()), rustc_hir::Node::AnonConst(_))
        };
        if is_anon_const(a) {
            Less
        } else if is_anon_const(b) {
            Equal
        } else {
            Greater
        }
    });

    let thirs: std::collections::HashMap<
        rustc_span::def_id::LocalDefId,
        (rustc_middle::thir::Thir<'tcx>, ExprId),
    > = bodies
        .into_iter()
        .map(|did| {
            let (thir, expr) = tcx
                .thir_body(rustc_middle::ty::WithOptConstParam {
                    did,
                    const_param_did: None,
                })
                .expect("While trying to reach a body's THIR defintion, got a typechecking error");
            // Borrowing `Thir` from a `Steal`!
            (did, (thir.borrow().clone(), expr))
        })
        .collect();

    let items = hir.items();
    let macro_calls_r = box macro_calls;
    let state = circus_frontend_exporter::State {
        tcx,
        options: box options.clone(),
        thir: (),
        owner_id: (),
        opt_def_id: None,
        macro_infos: macro_calls_r,
        local_ident_map: Rc::new(RefCell::new(HashMap::new())),
        cached_thirs: thirs,
        exported_spans: Rc::new(RefCell::new(HashSet::new())),
    };

    let result = circus_frontend_exporter::inline_macro_invokations(&items.collect(), &state);
    let exported_spans = state.exported_spans.borrow().clone();
    (exported_spans.into_iter().collect(), result)
}

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

const ENGINE_BINARY_NAME: &str = "circus-engine";
const ENGINE_BINARY_NOT_FOUND: &str = const_format::formatcp!(
    "The binary [{}] was not found in your [PATH].",
    ENGINE_BINARY_NAME,
);

fn find_circus_engine() -> std::path::PathBuf {
    use which::which;

    which(ENGINE_BINARY_NAME)
        .ok()
        .or_else(|| {
            which("node").ok().and_then(|_| {
                if let Ok(true) = inquire::Confirm::new(&format!(
                    "{} Should I try to download it from GitHub?",
                    ENGINE_BINARY_NOT_FOUND,
                ))
                .with_default(true)
                .prompt()
                {
                    panic!("TODO: Downloading from GitHub is not supported yet.")
                } else {
                    None
                }
            })
        })
        .expect(&ENGINE_BINARY_NOT_FOUND)
}

pub(crate) struct RustcCommonCallbacks {
    pub options: circus_cli_options::Options,
}
impl Callbacks for RustcCommonCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        let options = self.options.clone();
        config.parse_sess_created = Some(Box::new(move |parse_sess| {
            parse_sess.env_depinfo.get_mut().insert((
                Symbol::intern("THIR_EXPORT_OPTIONS"),
                Some(Symbol::intern(&serde_json::to_string(&options).unwrap())),
            ));
        }));
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let parse_ast = queries.parse().unwrap().peek();
        let macro_calls = collect_macros(&parse_ast);
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let (spans, converted_items) =
                convert_thir(&self.options.clone().into(), macro_calls, tcx);

            use circus_cli_options::Command;
            match self.options.clone().backend {
                Command::JSON { output_file } => {
                    serde_json::to_writer_pretty(output_file.open_or_stdout(), &converted_items)
                        .unwrap()
                }
                Command::Backend(backend) => {
                    let engine_options = circus_cli_options::engine::Options {
                        backend,
                        input: converted_items,
                    };
                    let engine_binary_path = find_circus_engine();
                    let mut engine_subprocess = std::process::Command::new(engine_binary_path)
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
                    if !out.status.success() {
                        panic!("{} exited with non-zero code", ENGINE_BINARY_NAME);
                        std::process::exit(out.status.code().unwrap_or(-1));
                    }
                    let output: circus_cli_options::engine::Output =
                        serde_json::from_slice(out.stdout.as_slice()).unwrap_or_else(|_| {
                            panic!(
                                "{} outputed incorrect JSON {}",
                                ENGINE_BINARY_NAME,
                                String::from_utf8(out.stdout).unwrap()
                            )
                        });
                    let options_frontend =
                        box circus_frontend_exporter::options::Options::from(self.options.clone())
                            .clone();
                    let state = circus_frontend_exporter::State {
                        tcx,
                        options: options_frontend,
                        thir: (),
                        owner_id: (),
                        opt_def_id: None::<rustc_hir::def_id::DefId>,
                        macro_infos: Box::new(HashMap::new()),
                        local_ident_map: Rc::new(RefCell::new(HashMap::new())),
                        cached_thirs: HashMap::new(),
                        exported_spans: Rc::new(RefCell::new(HashSet::new())),
                    };
                    let session = compiler.session();
                    for d in output.diagnostics.clone() {
                        use circus_frontend_exporter::SInto;
                        session.span_err_with_code(
                            spans
                                .iter()
                                .find(|span| span.sinto(&state) == d.span)
                                .cloned()
                                .unwrap_or(rustc_span::DUMMY_SP),
                            format!("{:#?}", d),
                            rustc_errors::DiagnosticId::Error(d.kind.code().into()),
                        );
                    }
                    for file in output.files.clone() {
                        let mut path = self.options.output_dir.clone();
                        path.push(std::path::PathBuf::from(file.path));
                        std::fs::create_dir_all({
                            let mut parent = path.clone();
                            parent.pop();
                            parent
                        })
                        .unwrap();
                        println!("Write {:#?}", path);
                        std::fs::write(path, file.contents).expect("Unable to write file");
                    }
                }
            };
        });

        Compilation::Continue
    }
}
