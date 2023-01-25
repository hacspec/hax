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

fn browse_items<'hir>(
    options: &thir_export::Options,
    macro_calls: HashMap<rustc_span::Span, rustc_ast::ast::MacCall>,
    tcx: TyCtxt<'hir>,
) {
    let hir = tcx.hir();
    let items = hir.items();
    let macro_calls_r = box macro_calls;
    let state = &thir_export::State {
        tcx,
        options: box options.clone(),
        thir: (),
        def_id: (),
        macro_infos: macro_calls_r,
        local_ident_map: Rc::new(RefCell::new(HashMap::new())),
    };
    let converted_items = thir_export::inline_macro_invokations(&items.collect(), state);

    serde_json::to_writer_pretty(
        thir_export::utils::writer_of_path(&options.output_file),
        &converted_items,
    )
    .unwrap();
    // if options.output_file == "-" {
    //     // TODO, stream to fd stdout instead
    //     println!("{}", serde_json::to_string(&converted_items).unwrap());
    // } else {
    //     let output = std::fs::File::create(&options.output_file).unwrap();
    //     serde_json::to_writer_pretty(output, &converted_items).unwrap();
    // }
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
    let own_args: Vec<String> = [String::from(args[0].clone())]
        .into_iter()
        .chain(
            escape_string::split(&*std::env::var("THIR_EXPORT_ARGS").unwrap_or("".into()))
                .expect("Invalid value for the environement variable THIR_EXPORT_ARGS")
                .into_iter()
                .map(|x| String::from(x)),
        )
        .collect();

    let options = thir_export::Options::parse_from(own_args.iter());

    options
        .export_json_schema
        .as_ref()
        .map(thir_export::utils::export_schema_to);

    let mut rustc_args: Vec<String> = std::env::args().skip(1).collect();
    if !rustc_args.iter().any(|arg| arg.starts_with("--sysroot")) {
        rustc_args.extend(vec!["--sysroot".into(), rustc_sysroot()])
    };

    std::process::exit(rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&rustc_args, &mut DefaultCallbacks { options }).run()
    }))
}
