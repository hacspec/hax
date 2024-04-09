#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(concat_idents)]
#![feature(trait_alias)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unreachable_code)]
#![allow(dead_code)]
#![feature(macro_metavar_expr)]
#![feature(internal_output_capture)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_feature;
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

use std::collections::HashSet;

use exporter::ExtractionCallbacks;
use hax_lint::Type;

mod linter;
use linter::LinterCallbacks;

mod callbacks_wrapper;
mod features;
use callbacks_wrapper::*;
use features::*;

use const_format::formatcp;
use hax_cli_options::{BackendOptions, Command, ExporterCommand, ENV_VAR_OPTIONS_FRONTEND};

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

fn setup_logging() {
    use tracing_subscriber::prelude::*;
    let enable_colors = {
        /* Respect [never] in [RUST_LOG_STYLE] */
        !std::env::var("RUST_LOG_STYLE").is_ok_and(|style| style == "never")
    };
    let subscriber = tracing_subscriber::Registry::default()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(
            tracing_tree::HierarchicalLayer::new(2)
                .with_ansi(enable_colors)
                .with_indent_lines(true),
        );
    tracing::subscriber::set_global_default(subscriber).unwrap();
}

const HAX_VANILLA_RUSTC: &str = "HAX_VANILLA_RUSTC";

fn main() {
    setup_logging();

    let options: hax_cli_options::Options =
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

    // When `HAX_FEATURES_DETECTION_MODE` is set, we just detect
    // features for the current crate, output them in JSON on stderr
    // and exit immediately
    if std::env::var("HAX_FEATURES_DETECTION_MODE").is_ok() {
        use std::io::BufWriter;
        return serde_json::to_writer(
            BufWriter::new(std::io::stderr()),
            &Features::detect(&options, &rustc_args),
        )
        .unwrap();
    }

    let (vanilla_rustc, vanilla_rustc_never) = {
        let vanilla_rustc = std::env::var(HAX_VANILLA_RUSTC);
        let vanilla_rustc_never = vanilla_rustc == Ok("never".into());
        (
            !vanilla_rustc_never && vanilla_rustc.is_ok(),
            vanilla_rustc_never,
        )
    };

    // fetch the correct callback structure given the command, and
    // coerce options
    let is_primary_package = std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    let is_build_script = std::env::var("CARGO_CRATE_NAME") == Ok("build_script_build".to_string()); // FIXME: is there a more robust way to do this?
    let translate_package =
        !vanilla_rustc && !is_build_script && (options.deps || is_primary_package);
    let mut callbacks: Box<dyn Callbacks + Send> = if translate_package {
        match &options.command {
            Some(Command::ExporterCommand(command)) => Box::new(exporter::ExtractionCallbacks {
                inline_macro_calls: options.inline_macro_calls.clone(),
                command: command.clone(),
                macro_calls: std::collections::HashMap::new(),
            }),
            Some(Command::LintCommand(command)) => {
                let ltype = match command {
                    hax_cli_options::LinterCommand::Hacspec => Type::Hacspec,
                    hax_cli_options::LinterCommand::Rust => Type::Rust,
                };
                Box::new(LinterCallbacks::new(ltype))
            }
            None => {
                // hacspec lint
                Box::new(LinterCallbacks::new(Type::Rust))
            }
        }
    } else {
        struct CallbacksNoop;
        impl Callbacks for CallbacksNoop {}
        Box::new(CallbacksNoop)
    };

    if translate_package {
        // We want to enable certain features, but only if the crate
        // itself doesn't enable those
        let features = Features {
            adt_const_params: false,    // not useful for now
            generic_const_exprs: false, // not useful for now
            register_tool: true,
            registered_tools: HashSet::from_iter(
                vec![hax_lib_macros_types::HAX_TOOL.into()].into_iter(),
            ),
            auto_traits: true,
            negative_impls: true,
        } - Features::detect_forking();
        rustc_args = [rustc_args[0].clone()]
            .into_iter()
            .chain([
                "--cfg".into(),
                hax_lib_macros_types::HAX_CFG_OPTION_NAME.into(),
            ])
            .chain(match &options.command {
                Some(Command::ExporterCommand(ExporterCommand::Backend(BackendOptions {
                    backend,
                    ..
                }))) => vec!["--cfg".into(), format!("hax_backend_{backend}")],
                _ => vec![],
            })
            .chain(features.into_iter().map(|s| format!("-Zcrate-attr={}", s)))
            .chain(rustc_args[1..].iter().cloned())
            .collect();
    };

    let mut callbacks = CallbacksWrapper {
        sub: &mut *callbacks,
        options: hax_cli_options::Options {
            force_cargo_build: if translate_package {
                options.force_cargo_build
            } else {
                hax_cli_options::ForceCargoBuild::default()
            },
            ..options
        },
    };

    let exit_code = rustc_driver::catch_with_exit_code({
        let rustc_args = rustc_args.clone();
        move || rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks).run()
    });

    std::process::exit(
        if !vanilla_rustc_never && translate_package && exit_code == 0 {
            // When the hax translation is successful, we need to re-run
            // rustc. Indeed, hax translation doesn't actually build a
            // package: no `rlib` will be written on disk.
            self::vanilla_rustc()
        } else {
            exit_code
        },
    )
}

/// Re-run rustc without doing any hax translation. This ensures a
/// `rlib` is produced (when the crate compiles correctly).
fn vanilla_rustc() -> i32 {
    use std::process::{Command, Stdio};
    let output = Command::new(std::env::args().next().unwrap())
        .args(std::env::args().skip(1))
        .env(HAX_VANILLA_RUSTC, "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap()
        .wait_with_output()
        .unwrap();
    if output.status.success() {
        0
    } else {
        let stdout = &std::str::from_utf8(&output.stdout).unwrap();
        let stderr = &std::str::from_utf8(&output.stderr).unwrap();
        println!("{stdout}");
        eprintln!("{stderr}");
        output.status.code().unwrap_or(1)
    }
}
