use annotate_snippets::{Level, Message, Renderer};
use clap::Parser;
use colored::Colorize;
use hax_cli_options::*;
use hax_cli_options_engine::*;
use is_terminal::IsTerminal;
use std::fs;
use std::io::BufRead;
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
const ENGINE_BINARY_NOT_FOUND: &str = const_format::formatcp!(
    "The binary [{}] was not found in your [PATH].",
    ENGINE_BINARY_NAME,
);

/// Dynamically looks for binary [ENGINE_BINARY_NAME].  First, we
/// check whether [HAX_ENGINE_BINARY] is set, and use that if it
/// is. Then, we try to find [ENGINE_BINARY_NAME] in PATH. If not
/// found, detect whether nodejs is available, download the JS-compiled
/// engine and use it.
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
    options: &Options,
    backend: &BackendOptions,
) {
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

    serde_json::to_writer::<_, EngineOptions>(
        std::io::BufWriter::new(
            engine_subprocess
                .stdin
                .as_mut()
                .expect("Could not write on stdin"),
        ),
        &engine_options,
    )
    .unwrap();
    let out = engine_subprocess.wait_with_output().unwrap();
    if !out.status.success() {
        let title = format!(
            "hax: {} exited with non-zero code {}\nstdout: {}\n stderr: {}",
            ENGINE_BINARY_NAME,
            out.status.code().unwrap_or(-1),
            String::from_utf8(out.stdout).unwrap(),
            String::from_utf8(out.stderr).unwrap(),
        );
        report(Level::Error.title(&title));
        std::process::exit(1);
    }
    let output: Output = serde_json::from_slice(out.stdout.as_slice()).unwrap_or_else(|_| {
        panic!(
            "{} outputed incorrect JSON {}",
            ENGINE_BINARY_NAME,
            String::from_utf8(out.stdout).unwrap()
        )
    });
    let options_frontend = Options::from(options.clone());

    {
        let mut rctx = hax_diagnostics::report::ReportCtx::default();
        for diag in &output.diagnostics {
            diag.with_message(&mut rctx, &working_dir, Level::Error, report);
        }
    }
    if backend.dry_run {
        serde_json::to_writer(std::io::BufWriter::new(std::io::stdout()), &output).unwrap()
    } else {
        let relative_path: PathBuf = [
            "proofs",
            format!("{}", backend.backend).as_str(),
            "extraction",
        ]
        .iter()
        .collect();
        let out_dir = manifest_dir.join(&relative_path);
        for file in output.files.clone() {
            let path = out_dir.join(&file.path);
            std::fs::create_dir_all(&path.parent().unwrap()).unwrap();
            std::fs::write(&path, file.contents).unwrap();
            let title = format!("hax: wrote file {}", path.display());
            report(Level::Info.title(&title))
        }
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
            Some(DebugEngineMode::File(file)) if !backend.dry_run => {
                println!("{}", debug_json)
            }
            _ => (),
        }
    }
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
fn run_command(options: &Options, haxmeta_files: Vec<EmitHaxMetaMessage>) {
    match options.command.clone() {
        Command::JSON {
            output_file,
            kind,
            include_extra,
            ..
        } => {
            use {with_kind_type, HaxMeta};
            with_kind_type!(kind, <Body>|| {
                for EmitHaxMetaMessage { path, .. } in haxmeta_files {
                    let file = std::io::BufReader::new(fs::File::open(&path).unwrap());
                    let haxmeta: HaxMeta<Body> = ciborium::from_reader(file).unwrap();
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

            for EmitHaxMetaMessage {
                working_dir,
                manifest_dir,
                path,
            } in haxmeta_files
            {
                let file = std::io::BufReader::new(fs::File::open(&path).unwrap());
                let haxmeta: HaxMeta<Body> = ciborium::from_reader(file).unwrap();

                run_engine(haxmeta, working_dir, manifest_dir, &options, &backend);
            }
        }
    }
}

fn main() {
    let args: Vec<String> = get_args("hax");
    let mut options = Options::parse_from(args.iter());
    options.normalize_paths();

    let (haxmeta_files, exit_code) = compute_haxmeta_files(&options);
    run_command(&options, haxmeta_files);

    std::process::exit(exit_code)
}
