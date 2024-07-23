use annotate_snippets::{Level, Message, Renderer};
use clap::Parser;
use colored::Colorize;
use hax_types::cli_options::*;
use hax_types::driver_api::*;
use hax_types::engine_api::*;
use is_terminal::IsTerminal;
use serde_jsonlines::BufReadExt;
use std::fs;
use std::io::BufRead;
use std::io::Write;
use std::path::PathBuf;
use std::process;

/// Return a toolchain argument to pass to `cargo`: when the correct nightly is
/// already present, this is None, otherwise we (1) ensure `rustup` is available
/// (2) install the nightly (3) return the toolchain
fn toolchain() -> Option<&'static str> {
    let current_rustc_version = version_check::triple()
        .map(|(_, channel, date)| format!("{channel}-{date}"))
        .unwrap_or("unknown".into());
    if env!("HAX_RUSTC_VERSION") != current_rustc_version {
        const TOOLCHAIN: &str = env!("HAX_TOOLCHAIN");
        // ensure rustup is available
        which::which("rustup").ok().unwrap_or_else(|| {
            println!("Error: {} was not found, but toolchain {} is required while the current toolchain is {}\n\nExiting.", "rustup".bold(), TOOLCHAIN.bold(), current_rustc_version.bold());
            std::process::exit(1)
        });
        // make sure the toolchain is installed
        rustup_toolchain::install(TOOLCHAIN).unwrap();
        // return the correct toolchain
        Some(TOOLCHAIN)
    } else {
        None
    }
}

/// [`get_args`] is a wrapper of `std::env::args` that strips a possible
/// cargo subcommand. This allows for a binary `BINARY` to be called
/// both with `cargo BINARY args...` and `cargo-BINARY args...`.
pub fn get_args(subcommand: &str) -> Vec<String> {
    let mut args: Vec<_> = std::env::args().collect();
    if args.get(1) == Some(&subcommand.to_string()) {
        // we face a call `cargo [subcommand]`: we need to get rid of the first argument
        args = args.into_iter().skip(1).collect();
    }
    args
}

/// Our custom rustc driver will *not* be run in an proper terminal,
/// thus logs would appear uncolored. When no `RUST_LOG_STYLE` env. var.
/// is set, [`rust_log_style`] checks wether the `cargo hax` command was
/// run inside a terminal. If it was inside a terminal,
/// [`rust_log_style`] returns `"always"`, which is the usual default
/// behavior. Otherwise we return `"never"`. When [`RUST_LOG_STYLE`] is
/// set, we just return its value.
const RUST_LOG_STYLE: &str = "RUST_LOG_STYLE";
fn rust_log_style() -> String {
    std::env::var(RUST_LOG_STYLE).unwrap_or_else(|_| {
        if std::io::stderr().is_terminal() {
            "always".to_string()
        } else {
            "never".to_string()
        }
    })
}

/// We set `cfg(hax)` so that client crates can include dependencies
/// or cfg-gate pieces of code.
const RUSTFLAGS: &str = "RUSTFLAGS";
fn rustflags() -> String {
    let rustflags = std::env::var(RUSTFLAGS).unwrap_or("".into());
    [rustflags, "--cfg hax".into()].join(" ")
}

const ENGINE_BINARY_NAME: &str = "hax-engine";
const ENGINE_BINARY_NOT_FOUND: &str = "The binary [hax-engine] was not found in your [PATH].";

/// Dynamically looks for binary [ENGINE_BINARY_NAME].  First, we
/// check whether [HAX_ENGINE_BINARY] is set, and use that if it
/// is. Then, we try to find [ENGINE_BINARY_NAME] in PATH. If not
/// found, detect whether nodejs is available, download the JS-compiled
/// engine and use it.
#[allow(unused_variables, unreachable_code)]
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
            let message = format!("hax: {}\n{}\n\n{} {}\n",
                      &ENGINE_BINARY_NOT_FOUND,
                      "Please make sure the engine is installed and is in PATH!",
                      "Hint: With OPAM, `eval $(opam env)` is necessary for OPAM binaries to be in PATH: make sure to run `eval $(opam env)` before running `cargo hax`.".bright_black(),
                      format!("(diagnostics: {})", if is_opam_setup_correctly() { "opam seems okay ✓" } else {"opam seems not okay ❌"}).bright_black()
            );
            report(Level::Error.title(&message));
            std::process::exit(2);
        })
}

/// Report an `annotate_snippets::Message` now
fn report(message: Message) {
    let renderer = Renderer::styled();
    eprintln!("{}", renderer.render(message))
}

/// Runs `hax-engine`
fn run_engine(
    haxmeta: HaxMeta<hax_frontend_exporter::ThirBody>,
    working_dir: PathBuf,
    manifest_dir: PathBuf,
    backend: &BackendOptions,
) -> bool {
    let engine_options = EngineOptions {
        backend: backend.clone(),
        input: haxmeta.items,
        impl_infos: haxmeta.impl_infos,
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

    let mut error = false;
    let mut output = Output {
        diagnostics: vec![],
        files: vec![],
        debug_json: None,
    };
    {
        let mut rctx = hax_types::diagnostics::report::ReportCtx::default();
        let mut stdin = std::io::BufWriter::new(
            engine_subprocess
                .stdin
                .as_mut()
                .expect("Could not write on stdin"),
        );

        macro_rules! send {
            ($value:expr) => {
                serde_json::to_writer(&mut stdin, $value).unwrap();
                stdin.write_all(b"\n").unwrap();
                stdin.flush().unwrap();
            };
        }

        send!(&engine_options);

        let out_dir = backend.output_dir.clone().unwrap_or({
            let relative_path: PathBuf = [
                "proofs",
                format!("{}", backend.backend).as_str(),
                "extraction",
            ]
            .iter()
            .collect();
            manifest_dir.join(&relative_path)
        });

        let stdout = std::io::BufReader::new(engine_subprocess.stdout.take().unwrap());
        for msg in stdout.json_lines() {
            let msg = msg.expect(
                "Hax engine sent an invalid json value. \
            This might be caused by debug messages on stdout, \
            which is reserved for JSON communication with cargo-hax",
            );
            use protocol::*;
            match msg {
                FromEngine::Exit => break,
                FromEngine::Diagnostic(diag) => {
                    error = true;
                    if backend.dry_run {
                        output.diagnostics.push(diag.clone())
                    }
                    diag.with_message(&mut rctx, &working_dir, Level::Error, report);
                }
                FromEngine::File(file) => {
                    if backend.dry_run {
                        output.files.push(file)
                    } else {
                        let path = out_dir.join(&file.path);
                        std::fs::create_dir_all(&path.parent().unwrap()).unwrap();
                        std::fs::write(&path, file.contents).unwrap();
                        let title = format!("hax: wrote file {}", path.display());
                        report(Level::Info.title(&title))
                    }
                }
                FromEngine::DebugString(debug) => {
                    output.debug_json = Some(debug);
                }
                FromEngine::PrettyPrintDiagnostic(diag) => {
                    send!(&ToEngine::PrettyPrintedDiagnostic(format!("{}", diag)));
                }
                FromEngine::PrettyPrintRust(code) => {
                    let code = match syn::parse_file(&code) {
                        Ok(file) => match std::panic::catch_unwind(|| prettyplease::unparse(&file))
                        {
                            Ok(pp) => Ok(pp),
                            Err(err) => Err(format!("prettyplease panicked with: {:#?}", err)),
                        },
                        Err(err) => Err(format!("{}", err)),
                    };
                    send!(&ToEngine::PrettyPrintedRust(code));
                }
                FromEngine::Ping => {
                    send!(&ToEngine::Pong);
                }
            }
        }
        drop(stdin);
    }

    let exit_status = engine_subprocess.wait().unwrap();
    if !exit_status.success() {
        let title = format!(
            "hax: {} exited with non-zero code {}",
            ENGINE_BINARY_NAME,
            exit_status.code().unwrap_or(-1),
        );
        report(Level::Error.title(&title));
        std::process::exit(1);
    }

    if backend.dry_run {
        serde_json::to_writer(std::io::BufWriter::new(std::io::stdout()), &output).unwrap()
    }
    if let Some(debug_json) = &output.debug_json {
        use DebugEngineMode;
        match &backend.debug_engine {
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
            Some(DebugEngineMode::File(_file)) if !backend.dry_run => {
                println!("{}", debug_json)
            }
            _ => (),
        }
    }

    error
}

/// Uses `cargo metadata` to compute a derived target directory.
fn target_dir(suffix: &str) -> PathBuf {
    let metadata = cargo_metadata::MetadataCommand::new().exec().unwrap();
    let mut dir = metadata.target_directory;
    dir.push(suffix);
    dir.into()
}

/// Calls `cargo` with a custom driver which computes `haxmeta` files
/// in `TARGET`. One `haxmeta` file is produced by crate. Each
/// `haxmeta` file contains the full AST of one crate.
fn compute_haxmeta_files(options: &Options) -> (Vec<EmitHaxMetaMessage>, i32) {
    let mut cmd = {
        let mut cmd = process::Command::new("cargo");
        if let Some(toolchain) = toolchain() {
            cmd.env("RUSTUP_TOOLCHAIN", toolchain);
        }
        cmd.args(["build".into()].iter().chain(options.cargo_flags.iter()));
        const COLOR_FLAG: &str = "--color";
        let explicit_color_flag = options.cargo_flags.iter().any(|flag| flag == COLOR_FLAG);
        if !explicit_color_flag && std::io::stderr().is_terminal() {
            cmd.args([COLOR_FLAG, "always"]);
        }
        cmd.stderr(std::process::Stdio::piped());
        if !options.no_custom_target_directory {
            cmd.env("CARGO_TARGET_DIR", target_dir("hax"));
        };
        cmd.env(
            "RUSTC_WORKSPACE_WRAPPER",
            std::env::var("HAX_RUSTC_DRIVER_BINARY")
                .unwrap_or("driver-hax-frontend-exporter".into()),
        )
        .env(RUST_LOG_STYLE, rust_log_style())
        .env(RUSTFLAGS, rustflags())
        .env(
            ENV_VAR_OPTIONS_FRONTEND,
            serde_json::to_string(&options)
                .expect("Options could not be converted to a JSON string"),
        );
        cmd
    };

    let mut child = cmd.spawn().unwrap();
    let haxmeta_files = {
        let mut haxmeta_files = vec![];
        let stderr = child.stderr.take().unwrap();
        let stderr = std::io::BufReader::new(stderr);
        for line in std::io::BufReader::new(stderr).lines() {
            if let Ok(line) = line {
                if let Some(msg) = line.strip_prefix(HAX_DRIVER_STDERR_PREFIX) {
                    use HaxDriverMessage;
                    let msg = serde_json::from_str(msg).unwrap();
                    match msg {
                        HaxDriverMessage::EmitHaxMeta(data) => haxmeta_files.push(data),
                    }
                } else {
                    eprintln!("{}", line);
                }
            }
        }
        haxmeta_files
    };

    let status = child
        .wait()
        .expect("`driver-hax-frontend-exporter`: could not start?");

    let exit_code = if !status.success() {
        let title = format!("hax: running `cargo build` was not successful, continuing anyway.");
        report(Level::Warning.title(&title));
        status.code().unwrap_or(254)
    } else {
        0
    };
    (haxmeta_files, exit_code)
}

/// Run the command given by the user
fn run_command(options: &Options, haxmeta_files: Vec<EmitHaxMetaMessage>) -> bool {
    match options.command.clone() {
        Command::JSON {
            output_file,
            kind,
            include_extra,
            ..
        } => {
            with_kind_type!(kind, <Body>|| {
                for EmitHaxMetaMessage { path, .. } in haxmeta_files {
                    let haxmeta: HaxMeta<Body> = HaxMeta::read(fs::File::open(&path).unwrap());
                    let dest = output_file.open_or_stdout();
                    (if include_extra {
                        serde_json::to_writer(
                            dest,
                            &WithDefIds {
                                def_ids: haxmeta.def_ids,
                                impl_infos: haxmeta.impl_infos,
                                items: haxmeta.items,
                            },
                        )
                    } else {
                        serde_json::to_writer(dest, &haxmeta.items)
                    })
                        .unwrap()
                }
            });
            false
        }
        Command::Backend(backend) => {
            use hax_frontend_exporter::ThirBody as Body;
            use Backend;

            if matches!(backend.backend, Backend::Easycrypt | Backend::ProVerif(..)) {
                let title = format!(
                    "hax: Experimental backend \"{}\" is work in progress.",
                    backend.backend
                );
                report(Level::Warning.title(&title))
            }

            let mut error = false;
            for EmitHaxMetaMessage {
                working_dir,
                manifest_dir,
                path,
            } in haxmeta_files
            {
                let haxmeta: HaxMeta<Body> = HaxMeta::read(fs::File::open(&path).unwrap());

                error = error || run_engine(haxmeta, working_dir, manifest_dir, &backend);
            }
            error
        }
    }
}

fn main() {
    let args: Vec<String> = get_args("hax");
    let mut options = Options::parse_from(args.iter());
    options.normalize_paths();

    let (haxmeta_files, exit_code) = compute_haxmeta_files(&options);
    let error = run_command(&options, haxmeta_files);

    std::process::exit(if exit_code == 0 && error {
        1
    } else {
        exit_code
    })
}
