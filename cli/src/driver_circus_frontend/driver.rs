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
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

mod exporter;

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
    let options: circus_cli_options::Options =
        serde_json::from_str(&std::env::var(ENV_VAR_OPTIONS_FRONTEND).expect(&format!(
            "Cannot find environnement variable {}",
            ENV_VAR_OPTIONS_FRONTEND
        )))
        .expect(&format!(
            "Invalid value for the environnement variable {}",
            ENV_VAR_OPTIONS_FRONTEND
        ));

    let mut rustc_args: Vec<String> = std::env::args().skip(1).collect();
    if !rustc_args.iter().any(|arg| arg.starts_with("--sysroot")) {
        rustc_args.extend(vec!["--sysroot".into(), rustc_sysroot()])
    };

    std::process::exit(rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&rustc_args, &mut exporter::RustcCommonCallbacks { options })
            .run()
    }))
}
