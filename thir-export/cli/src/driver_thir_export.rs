#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(concat_idents)]
#![feature(trait_alias)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unreachable_code)]
#![allow(dead_code)]
#![feature(macro_metavar_expr)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_analysis;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_lint_defs;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

use rustc_ast::ast;
use rustc_data_structures::sync::Lrc;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::DiagnosticId;
use rustc_hir::hir_id::HirId;
use rustc_interface::{interface::Compiler, Queries};
use rustc_lint::{EarlyContext, EarlyLintPass, LateContext, LateLintPass, LintPass};
use rustc_lint_defs::{declare_lint, declare_lint_pass};
use rustc_middle::middle::region::Scope;
use rustc_session::Session;

use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    thir,
    thir::{Block, BlockId, Expr, ExprId, ExprKind, Pat, PatKind, Stmt, StmtId, StmtKind, Thir},
};
// mod thir_ast;

// mod translate;
// #[macro_use]
// mod sinto;
// use sinto::*;
// mod items_ast;
// mod options;
// use options::Options;

use thir_export::{self};

use std::cell::RefCell;
use std::rc::Rc;

fn browse_items<'tcx>(
    options: &thir_export::Options,
    macro_calls: HashMap<rustc_span::Span, rustc_ast::ast::MacCall>,
    tcx: TyCtxt<'tcx>,
) {
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
    let state = &thir_export::State {
        tcx,
        options: box options.clone(),
        thir: (),
        def_id: (),
        opt_def_id: None,
        macro_infos: macro_calls_r,
        local_ident_map: Rc::new(RefCell::new(HashMap::new())),
        cached_thirs: thirs,
    };
    let converted_items = thir_export::inline_macro_invokations(&items.collect(), state);

    serde_json::to_writer_pretty(options.output_file.open_or_stdout(), &converted_items).unwrap();
}

use std::collections::HashMap;

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

fn linter(crate_ast: &rustc_ast::ast::Crate, session: &Lrc<Session>, compiler: &Compiler) {
    use {rustc_ast::ast::*, rustc_ast::visit::*, rustc_span::Span};

    struct ExprLinter<'a> {
        session: &'a Lrc<Session>,
    }
    impl<'ast, 'a> Visitor<'ast> for ExprLinter<'a> {
        fn visit_expr(&mut self, ex: &'ast Expr) {
            match &ex.kind {
                ExprKind::Block(block, _) => match block.rules {
                    rustc_ast::ast::BlockCheckMode::Unsafe(
                        rustc_ast::ast::UnsafeSource::UserProvided,
                    ) => {
                        self.session.span_warn_with_code(
                            block.span,
                            "[Circus] Unsafe code is not supported",
                            DiagnosticId::Lint {
                                name: "Unsafe code".to_string(),
                                has_future_breakage: true,
                                is_force_warn: true,
                            },
                        );
                    }
                    _ => (),
                },
                _ => (), // eprintln!("found expression {:?} at {:?}", ex.kind, ex.span),
            }
        }
    }
    let mut linter = ExprLinter { session };
    linter.visit_crate(crate_ast);

    struct FnLinter<'a> {
        session: &'a Lrc<Session>,
    }
    impl<'a> FnLinter<'a> {
        fn no_trait_objects(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] Trait objects are not supported",
                DiagnosticId::Lint {
                    name: "Trait objects".to_string(),
                    has_future_breakage: true,
                    is_force_warn: true,
                },
            );
        }
    }
    impl<'ast, 'a> Visitor<'ast> for FnLinter<'a> {
        fn visit_fn(&mut self, fk: FnKind<'ast>, _: Span, _: NodeId) {
            match fk {
                FnKind::Fn(_, ident, sig, ..) => {
                    // eprintln!(" ... found function {:?} at {:?}", ident.name, ident.span);
                    // Unsafe functions
                    match sig.header.unsafety {
                        ast::Unsafe::Yes(span) => {
                            self.session.span_warn_with_code(
                                span,
                                "[Circus] Unsafe functions are not supported",
                                DiagnosticId::Lint {
                                    name: "Unsafe code".to_string(),
                                    has_future_breakage: true,
                                    is_force_warn: true,
                                },
                            );
                        }
                        _ => (),
                    }
                    // async functions
                    match sig.header.asyncness {
                        ast::Async::Yes { span, .. } => {
                            self.session.span_warn_with_code(
                                span,
                                "[Circus] Async functions are not supported",
                                DiagnosticId::Lint {
                                    name: "Async code".to_string(),
                                    has_future_breakage: true,
                                    is_force_warn: true,
                                },
                            );
                        }
                        _ => (),
                    }
                    // XXX: ext?
                    // parameters
                    sig.decl.inputs.iter().for_each(|param| {
                        // eprintln!(
                        //     " >>> Checking {:?} with kind {:?}",
                        //     param.span, param.ty.kind
                        // );
                        // No dyn/trait object
                        match &param.ty.kind {
                            ast::TyKind::TraitObject(_, _) => {
                                self.no_trait_objects(param.ty.span);
                            }
                            ast::TyKind::Rptr(_, ty) => match ty.ty.kind {
                                ast::TyKind::TraitObject(_, _) => {
                                    self.no_trait_objects(param.ty.span);
                                }
                                ast::TyKind::ImplTrait(_, _) => {
                                    self.no_trait_objects(param.ty.span);
                                }
                                _ => (),
                            },
                            ast::TyKind::ImplTrait(_, _) => {
                                self.no_trait_objects(param.ty.span);
                            }
                            _ => (), // eprintln!("    param ty {:?}", param.ty.kind),
                        }
                    });
                }
                FnKind::Closure(..) => {
                    // eprintln!("found a closure - unsupported?");
                }
            }
        }
    }
    let mut linter = FnLinter { session };
    linter.visit_crate(crate_ast);

    struct ItemLinter {}
    impl<'ast> Visitor<'ast> for ItemLinter {
        fn visit_item(&mut self, i: &'ast Item) {
            // eprintln!("found item {:?} at {:?}", i.ident.name, i.span);
        }
    }
    let mut linter = ItemLinter {};
    linter.visit_crate(crate_ast);

    // struct Linter<'a> {
    //     session: &'a Lrc<Session>,
    // }
    // impl<'a> LintPass for Linter<'a> {
    //     fn name(&self) -> &'static str {
    //         "Circus"
    //     }
    // }
    // impl<'tcx, 'a> LateLintPass<'tcx> for Linter<'a> {
    //     fn check_fn(
    //         &mut self,
    //         _: &LateContext<'tcx>,
    //         _: rustc_hir::intravisit::FnKind<'tcx>,
    //         _: &'tcx rustc_hir::FnDecl<'tcx>,
    //         _: &'tcx rustc_hir::Body<'tcx>,
    //         _: Span,
    //         _: HirId,
    //     ) {
    //         eprintln!(" >>> late lint pass check fn");
    //     }
    // }
    // let mut linter = Linter { session };
    // compiler.register_lints();
}

struct DefaultCallbacks {
    options: thir_export::Options,
}

impl Callbacks for DefaultCallbacks {
    // fn config(&mut self, config: &mut rustc_interface::Config) {}
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
        let session = compiler.session();
        let macro_calls = collect_macros(&queries.parse().unwrap().peek());
        linter(&queries.parse().unwrap().peek(), session, compiler);
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| browse_items(&self.options, macro_calls, tcx));

        Compilation::Continue
    }
}

fn rustc_sysroot() -> String {
    std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap()
}

use clap::Parser;
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let options: thir_export::Options = serde_json::from_str(
        &std::env::var("THIR_EXPORT_OPTIONS")
            .expect("Cannot find environnement variable THIR_EXPORT_OPTIONS"),
    )
    .expect("Invalid value for the environnement variable THIR_EXPORT_OPTIONS");

    let mut rustc_args: Vec<String> = std::env::args().skip(1).collect();
    if !rustc_args.iter().any(|arg| arg.starts_with("--sysroot")) {
        rustc_args.extend(vec!["--sysroot".into(), rustc_sysroot()])
    };

    std::process::exit(rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&rustc_args, &mut DefaultCallbacks { options }).run()
    }))
}
