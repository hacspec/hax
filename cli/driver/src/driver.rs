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
use circus_lint::Type;
use exporter::ExtractionCallbacks;

mod linter;
use linter::LinterCallbacks;

use circus_cli_options::{Command, ENV_VAR_OPTIONS_FRONTEND};
use const_format::formatcp;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface, Queries};
use rustc_span::symbol::Symbol;

fn rustc_sysroot() -> String {
    std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap()
}

/// Wraps a [Callbacks] structure, and injects some cache-related
/// configuration in the `config` phase of rustc
struct CallbacksWrapper<'a> {
    sub: &'a mut (dyn Callbacks + Send + 'a),
    options: circus_cli_options::Options,
}
impl<'a> Callbacks for CallbacksWrapper<'a> {
    fn config(&mut self, config: &mut interface::Config) {
        let options = self.options.clone();
        config.parse_sess_created = Some(Box::new(move |parse_sess| {
            parse_sess.env_depinfo.get_mut().insert((
                Symbol::intern(circus_cli_options::ENV_VAR_OPTIONS_FRONTEND),
                Some(Symbol::intern(&serde_json::to_string(&options).unwrap())),
            ));
        }));
        self.sub.config(config)
    }
    fn after_parsing<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_parsing(compiler, queries)
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_expansion(compiler, queries)
    }
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.sub.after_analysis(compiler, queries)
    }
}

fn main() {
    let _ = pretty_env_logger::try_init();

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
    let mut callbacks: Box<dyn Callbacks + Send> = match &options.command {
        Some(Command::ExporterCommand(command)) => Box::new(exporter::ExtractionCallbacks {
            inline_macro_calls: options.inline_macro_calls.clone(),
            command: command.clone(),
        }),
        Some(Command::LintCommand(command)) => {
            let ltype = match command {
                circus_cli_options::LinterCommand::Hacspec => Type::Hacspec,
                circus_cli_options::LinterCommand::Rust => Type::Rust,
            };
            Box::new(LinterCallbacks::new(ltype))
        }
        None => {
            // hacspec lint
            Box::new(LinterCallbacks::new(Type::Rust))
        }
    };

    let mut callbacks = CallbacksWrapper {
        sub: &mut *callbacks,
        options,
    };

    std::process::exit(rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks).run()
    }))
}
