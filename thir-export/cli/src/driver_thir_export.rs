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
        owner_id: (),
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
            rustc_ast::visit::walk_mac(self, mac);
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

    struct AstLinter<'a> {
        session: &'a Lrc<Session>,
    }
    impl<'ast, 'a> Visitor<'ast> for AstLinter<'a> {
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
                                has_future_breakage: false,
                                is_force_warn: true,
                            },
                        );
                    }
                    _ => (),
                },
                ExprKind::While(e, b, l) => self.unsupported_loop(b.span),
                ExprKind::Loop(e, b, l) => self.unsupported_loop(e.span),
                ExprKind::Async(e, c, b) => self.no_async_await(b.span),
                ExprKind::Await(a) => self.no_async_await(a.span),
                ExprKind::InlineAsm(p) => self.no_unsafe(p.line_spans[0]),
                _ => (), // eprintln!("found expression {:?} at {:?}", ex.kind, ex.span),
            }

            // keep going
            rustc_ast::visit::walk_expr(self, ex);
        }

        fn visit_item(&mut self, i: &'ast Item) {
            eprintln!("found item {:?} at {:?}", i.ident.name, i.span);
            match i.kind {
                rustc_ast::ast::ItemKind::Union(_, _) => {
                    // TODO: This should be an error (span_err_with_code)
                    self.session.span_warn_with_code(
                        i.span,
                        "[Circus] Unions are not supported",
                        DiagnosticId::Lint {
                            name: "Unsupported item".to_string(),
                            has_future_breakage: false,
                            is_force_warn: true,
                        },
                    );
                }
                _ => (),
            }

            // keep going
            rustc_ast::visit::walk_item(self, i);
        }

        fn visit_fn(&mut self, fk: FnKind<'ast>, _: Span, _: NodeId) {
            match fk {
                FnKind::Fn(_, ident, sig, ..) => {
                    // eprintln!(" ... found function {:?} at {:?}", ident.name, ident.span);
                    // TODO: All this should be an error (span_err_with_code)
                    // Unsafe functions
                    match sig.header.unsafety {
                        ast::Unsafe::Yes(span) => {
                            self.no_unsafe(span);
                        }
                        _ => (),
                    }
                    // async functions
                    match sig.header.asyncness {
                        ast::Async::Yes { span, .. } => {
                            self.no_async_await(span);
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

            // keep going
            rustc_ast::visit::walk_fn(self, fk);
        }

        fn visit_assoc_item(&mut self, i: &'ast AssocItem, ctxt: AssocCtxt) {
            // eprintln!("found assoc item {:?} at {:?}", i.ident.name, i.span);
            match i.kind {
                rustc_ast::ast::AssocItemKind::Fn(_) => (),
                rustc_ast::ast::AssocItemKind::Const(_, _, _) => self.no_assoc_items(i.span),
                rustc_ast::ast::AssocItemKind::Type(_) => self.no_assoc_items(i.span),
                rustc_ast::ast::AssocItemKind::MacCall(_) => self.no_assoc_items(i.span),
            }

            // keep going
            rustc_ast::visit::walk_assoc_item(self, i, ctxt);
        }

        fn visit_stmt(&mut self, s: &'ast Stmt) {
            match &s.kind {
                ast::StmtKind::Local(b) => match &b.kind {
                    ast::LocalKind::Init(e) => match &e.kind {
                        ast::ExprKind::AddrOf(x, f, s) => {
                            // Don't allow raw borrows (pointer) and mutable borrows.
                            if matches!(x, ast::BorrowKind::Raw)
                                || matches!(f, ast::Mutability::Mut)
                            {
                                self.session.span_warn_with_code(
                                    e.span,
                                    "[Circus] Mutable borrows are not supported",
                                    DiagnosticId::Lint {
                                        name: "Mut borrow".to_string(),
                                        has_future_breakage: false,
                                        is_force_warn: true,
                                    },
                                );
                            }
                        }
                        _ => (),
                    },
                    _ => (),
                },
                ast::StmtKind::Item(_) => (),
                ast::StmtKind::Expr(_) => (),
                ast::StmtKind::Semi(_) => (),
                ast::StmtKind::Empty => (),
                ast::StmtKind::MacCall(_) => (),
            }

            // keep going
            rustc_ast::visit::walk_stmt(self, s);
        }

        fn visit_where_predicate(&mut self, p: &'ast WherePredicate) {
            match p {
                ast::WherePredicate::BoundPredicate(p) => self.no_where_predicate(p.span),
                ast::WherePredicate::RegionPredicate(p) => self.no_where_predicate(p.span),
                ast::WherePredicate::EqPredicate(p) => self.no_where_predicate(p.span),
            }

            // keep going
            rustc_ast::visit::walk_where_predicate(self, p);
        }

        fn visit_inline_asm(&mut self, asm: &'ast InlineAsm) {
            self.no_unsafe(asm.line_spans[0]); // XXX: can these crash?

            // keep going
            rustc_ast::visit::walk_inline_asm(self, asm);
        }

        fn visit_inline_asm_sym(&mut self, sym: &'ast InlineAsmSym) {
            self.no_unsafe(sym.path.span);

            // keep going
            rustc_ast::visit::walk_inline_asm_sym(self, sym);
        }

        fn visit_use_tree(&mut self, use_tree: &'ast UseTree, id: NodeId, _nested: bool) {
            eprintln!(" >>> Found use {:?}", use_tree);

            // keep going
            rustc_ast::visit::walk_use_tree(self, use_tree, id);
        }
    }
    let mut linter = AstLinter { session };
    linter.visit_crate(crate_ast);

    impl<'a> AstLinter<'a> {
        fn extern_crate(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] External crates are not supported",
                DiagnosticId::Lint {
                    name: "External".to_string(),
                    has_future_breakage: false,
                    is_force_warn: true,
                },
            );
        }

        fn no_trait_objects(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] Trait objects are not supported",
                DiagnosticId::Lint {
                    name: "Trait objects".to_string(),
                    has_future_breakage: false,
                    is_force_warn: true,
                },
            );
        }

        fn no_assoc_items(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] Associated items are not supported",
                DiagnosticId::Lint {
                    name: "Assoc items".to_string(),
                    has_future_breakage: false,
                    is_force_warn: true,
                },
            );
        }

        fn no_where_predicate(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] Where predicates are not supported",
                DiagnosticId::Lint {
                    name: "Where".to_string(),
                    has_future_breakage: false,
                    is_force_warn: true,
                },
            );
        }

        fn no_async_await(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] Async and await are not supported",
                DiagnosticId::Lint {
                    name: "Async".to_string(),
                    has_future_breakage: false,
                    is_force_warn: true,
                },
            );
        }

        fn no_unsafe(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] Unsafe code is not supported",
                DiagnosticId::Lint {
                    name: "Unsafe".to_string(),
                    has_future_breakage: false,
                    is_force_warn: true,
                },
            );
        }

        fn unsupported_loop(&self, span: Span) {
            self.session.span_warn_with_code(
                span,
                "[Circus] loop and while are not supported",
                DiagnosticId::Lint {
                    name: "Loops".to_string(),
                    has_future_breakage: false,
                    is_force_warn: true,
                },
            );
        }
    }

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

use rustc_interface::interface;
use rustc_session::parse::ParseSess;
use rustc_span::symbol::Symbol;

struct DefaultCallbacks {
    options: thir_export::Options,
}

impl Callbacks for DefaultCallbacks {
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
