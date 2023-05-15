use clap::{Parser, Subcommand};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

pub use circus_frontend_exporter_options::*;

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct ForceCargoBuild {
    pub data: u128,
}

impl std::convert::From<&std::ffi::OsStr> for ForceCargoBuild {
    fn from(s: &std::ffi::OsStr) -> Self {
        ForceCargoBuild {
            data: if s == "false" {
                use std::time::{SystemTime, UNIX_EPOCH};
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map(|r| r.as_millis())
                    .unwrap_or(0)
            } else {
                0
            },
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum PathOrDash {
    Dash,
    Path(PathBuf),
}

impl std::convert::From<&std::ffi::OsStr> for PathOrDash {
    fn from(s: &std::ffi::OsStr) -> Self {
        if s == "-" {
            PathOrDash::Dash
        } else {
            PathOrDash::Path(PathBuf::from(s))
        }
    }
}

impl PathOrDash {
    pub fn open_or_stdout(&self) -> Box<dyn std::io::Write> {
        match self {
            PathOrDash::Dash => Box::new(std::io::stdout()),
            PathOrDash::Path(path) => Box::new(std::fs::File::create(&path).unwrap()),
        }
    }
    pub fn map_path<F: FnOnce(&Path) -> PathBuf>(&self, f: F) -> Self {
        match self {
            PathOrDash::Path(path) => PathOrDash::Path(f(path)),
            PathOrDash::Dash => PathOrDash::Dash,
        }
    }
}

fn absolute_path(path: impl AsRef<std::path::Path>) -> std::io::Result<std::path::PathBuf> {
    use path_clean::PathClean;
    let path = path.as_ref();

    let absolute_path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()?.join(path)
    }
    .clean();

    Ok(absolute_path)
}

pub trait NormalizePaths {
    fn normalize_paths(self) -> Self;
}

impl NormalizePaths for PathBuf {
    fn normalize_paths(self) -> Self {
        absolute_path(self).unwrap()
    }
}
impl NormalizePaths for PathOrDash {
    fn normalize_paths(self) -> Self {
        match self {
            PathOrDash::Dash => PathOrDash::Dash,
            PathOrDash::Path(p) => PathOrDash::Path(p.normalize_paths()),
        }
    }
}

#[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
pub enum Backend {
    /// Use the F* backend
    Fstar,
    /// Use the Coq backend
    Coq,
    /// Use the EasyCrypt backend
    Easycrypt,
}

#[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
pub struct BackendOptions {
    #[command(subcommand)]
    backend: Backend,

    /// Directory in which the backend should output modules. If [-]
    /// (a dash) is given to this option, the modules will be printed
    /// on the stdout in JSON.
    #[arg(short, long = "output-dir", default_value = "out/")]
    pub output_dir: PathOrDash,
}

#[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
pub enum ExporterCommand {
    /// Translate to a backend
    #[clap(name = "into")]
    Backend(BackendOptions),

    /// Export directly as a JSON file
    JSON {
        /// Path to the output JSON file, "-" denotes stdout.
        #[arg(
            short,
            long = "output-file",
            default_value = "circus_frontend_export.json"
        )]
        output_file: PathOrDash,
    },
}

#[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
pub enum LinterCommand {
    /// Lint for the hacspec subset
    Hacspec,
    /// Lint for the supported Rust subset
    Rust,
}

#[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
pub enum Command {
    #[command(flatten)]
    ExporterCommand(ExporterCommand),
    #[clap(subcommand, name = "lint", about = "Lint the code")]
    LintCommand(LinterCommand),
}

#[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
#[command(author, version = concat!("commit=", env!("CIRCUS_GIT_COMMIT_HASH"), " ", "describe=", env!("CIRCUS_GIT_DESCRIBE")), name = "circus", about, long_about = None)]
pub struct Options {
    /// Replace the expansion of each macro matching PATTERN by their
    /// invocation. PATTERN denotes a rust path (i.e. [A::B::c]) in
    /// which glob patterns are allowed. The glob pattern * matches
    /// any name, the glob pattern ** matches zero, one or more
    /// names. For instance, [A::B::C::D::X] and [A::E::F::D::Y]
    /// matches [A::**::D::*].
    #[arg(
        short = 'i',
        long = "inline-macro-call",
        value_name = "PATTERN",
        value_parser,
        value_delimiter = ','
    )]
    pub inline_macro_calls: Vec<Namespace>,

    /// Semi-colon terminated list of arguments to pass to the
    /// [cargo build] invocation. For example, to apply this
    /// program on a package [foo], use [-C -p foo ;]. (make sure
    /// to escape [;] correctly in your shell)
    #[arg(default_values = Vec::<&str>::new(), short='C', allow_hyphen_values=true, num_args=1.., long="cargo-args", value_terminator=";")]
    pub cargo_flags: Vec<String>,

    #[command(subcommand)]
    pub command: Option<Command>,

    /// [cargo] caching is disabled by default, this flag enables it back.
    #[arg(long="enable-cargo-cache", action=clap::builder::ArgAction::SetTrue)]
    pub force_cargo_build: ForceCargoBuild,
}

impl NormalizePaths for ExporterCommand {
    fn normalize_paths(self) -> Self {
        use ExporterCommand::*;
        match self {
            JSON { output_file } => JSON {
                output_file: output_file.normalize_paths(),
            },
            Backend(o) => Backend(BackendOptions {
                output_dir: o.output_dir.normalize_paths(),
                ..o
            }),
        }
    }
}

impl NormalizePaths for Command {
    fn normalize_paths(self) -> Self {
        match self {
            Command::ExporterCommand(cmd) => Command::ExporterCommand(cmd.normalize_paths()),
            _ => self,
        }
    }
}
impl NormalizePaths for Options {
    fn normalize_paths(self) -> Self {
        Options {
            command: self.command.map(|c| c.normalize_paths()),
            ..self
        }
    }
}

impl From<Options> for circus_frontend_exporter_options::Options {
    fn from(opts: Options) -> circus_frontend_exporter_options::Options {
        circus_frontend_exporter_options::Options {
            inline_macro_calls: opts.inline_macro_calls,
        }
    }
}

pub const ENV_VAR_OPTIONS_FRONTEND: &str = "DRIVER_CIRCUS_FRONTEND_OPTS";
