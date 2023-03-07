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
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::middle::region::Scope;

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

use thir_export;

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
        }
    }
    let mut v = MacroCollector {
        macro_calls: HashMap::new(),
    };
    v.visit_crate(crate_ast);
    v.macro_calls
}

struct DefaultCallbacks {
    options: thir_export::Options,
}
impl Callbacks for DefaultCallbacks {
    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let macro_calls = collect_macros(&queries.parse().unwrap().peek());
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
