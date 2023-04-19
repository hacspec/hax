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
use circus_cli_options::Command;

use circus_cli_options::ENV_VAR_OPTIONS_FRONTEND;
use const_format::formatcp;

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
    let options: circus_cli_options::Options =
        serde_json::from_str(&std::env::var(ENV_VAR_OPTIONS_FRONTEND).expect(&formatcp!(
            "Cannot find environnement variable {}",
            ENV_VAR_OPTIONS_FRONTEND
        )))
        .expect(&formatcp!(
            "Invalid value for the environnement variable {}",
            ENV_VAR_OPTIONS_FRONTEND
        ));

    let mut rustc_args: Vec<String> = std::env::args().skip(1).collect();
    // add [--sysroot] if not present
    if !rustc_args.iter().any(|arg| arg.starts_with("--sysroot")) {
        rustc_args.extend(vec!["--sysroot".into(), rustc_sysroot()])
    };

    // fetch the correct callback structure given the command, and
    // coerce options
    let mut callback = match options.command {
        Command::ExporterCommand(command) => exporter::Options {
            output_dir: options.output_dir,
            inline_macro_calls: options.inline_macro_calls,
            command,
        },
    };

    std::process::exit(rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&rustc_args, &mut callback).run()
    }))
}
