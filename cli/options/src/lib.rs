use clap::{Parser, Subcommand, ValueEnum};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::path::{Path, PathBuf};

pub use hax_frontend_exporter_options::*;

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub enum DebugEngineMode {
    File(PathOrDash),
    Interactive,
}

impl std::convert::From<&str> for DebugEngineMode {
    fn from(s: &str) -> Self {
        match s {
            "i" | "interactively" => DebugEngineMode::Interactive,
            s => DebugEngineMode::File(s.strip_prefix("file:").unwrap_or(s).into()),
        }
    }
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct ForceCargoBuild {
    pub data: u128,
}

impl std::default::Default for ForceCargoBuild {
    fn default() -> Self {
        ForceCargoBuild { data: 0 }
    }
}

impl std::convert::From<&str> for ForceCargoBuild {
    fn from(s: &str) -> Self {
        use std::time::{SystemTime, UNIX_EPOCH};
        if s == "false" {
            ForceCargoBuild {
                data: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map(|r| r.as_millis())
                    .unwrap_or(0),
            }
        } else {
            ForceCargoBuild::default()
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum PathOrDash {
    Dash,
    Path(PathBuf),
}

impl std::convert::From<&str> for PathOrDash {
    fn from(s: &str) -> Self {
        match s {
            "-" => PathOrDash::Dash,
            _ => PathOrDash::Path(PathBuf::from(s)),
        }
    }
}

impl PathOrDash {
    pub fn open_or_stdout(&self) -> Box<dyn std::io::Write> {
        use std::io::BufWriter;
        match self {
            PathOrDash::Dash => Box::new(BufWriter::new(std::io::stdout())),
            PathOrDash::Path(path) => {
                Box::new(BufWriter::new(std::fs::File::create(&path).unwrap()))
            }
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
    fn normalize_paths(&mut self);
}

impl NormalizePaths for PathBuf {
    fn normalize_paths(&mut self) {
        *self = absolute_path(&self).unwrap();
    }
}
impl NormalizePaths for PathOrDash {
    fn normalize_paths(&mut self) {
        match self {
            PathOrDash::Path(p) => p.normalize_paths(),
            PathOrDash::Dash => (),
        }
    }
}

#[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
pub struct ProVerifOptions {
    /// Items for which hax should extract a default-valued process
    /// macro with a corresponding type signature. This flag expects a
    /// space-separated list of inclusion clauses. An inclusion clause
    /// is a Rust path prefixed with `+`, `+!` or `-`. `-` means
    /// implementation only, `+!` means interface only and `+` means
    /// implementation and interface. Rust path chunks can be either a
    /// concrete string, or a glob (just like bash globs, but with
    /// Rust paths).
    #[arg(
        long,
        value_parser = parse_inclusion_clause,
        value_delimiter = ' ',
        allow_hyphen_values(true)
    )]
    assume_items: Vec<InclusionClause>,
}

#[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
pub struct FStarOptions {
    /// Set the Z3 per-query resource limit
    #[arg(long, default_value = "15")]
    z3rlimit: u32,
    /// Number of unrolling of recursive functions to try
    #[arg(long, default_value = "0")]
    fuel: u32,
    /// Number of unrolling of inductive datatypes to try
    #[arg(long, default_value = "1")]
    ifuel: u32,
    /// Modules for which Hax should extract interfaces (`*.fsti`
    /// files) in supplement to implementations (`*.fst` files). By
    /// default we extract no interface, only implementations. This
    /// flag expects a space-separated list of inclusion clauses. An
    /// inclusion clause is a Rust path prefixed with `+`, `+!` or
    /// `-`. `-` means implementation only, `+!` means interface only
    /// and `+` means implementation and interface. Rust path chunks
    /// can be either a concrete string, or a glob (just like bash
    /// globs, but with Rust paths).
    #[arg(
        long,
        value_parser = parse_inclusion_clause,
        value_delimiter = ' ',
        allow_hyphen_values(true)
    )]
    interfaces: Vec<InclusionClause>,
}

#[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
pub enum Backend {
    /// Use the F* backend
    Fstar(FStarOptions),
    /// Use the Coq backend
    Coq,
    /// Use the SSProve backend
    Ssprove,
    /// Use the EasyCrypt backend (warning: work in progress!)
    Easycrypt,
    /// Use the ProVerif backend (warning: work in progress!)
    ProVerif(ProVerifOptions),
}

impl fmt::Display for Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Backend::Fstar(..) => write!(f, "fstar"),
            Backend::Coq => write!(f, "coq"),
            Backend::Ssprove => write!(f, "ssprove"),
            Backend::Easycrypt => write!(f, "easycrypt"),
            Backend::ProVerif(..) => write!(f, "proverif"),
        }
    }
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
enum DepsKind {
    Transitive,
    Shallow,
    None,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
enum InclusionKind {
    /// `+query` include the items selected by `query`
    Included(DepsKind),
    Excluded,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
struct InclusionClause {
    kind: InclusionKind,
    namespace: Namespace,
}

fn parse_inclusion_clause(
    s: &str,
) -> Result<InclusionClause, Box<dyn std::error::Error + Send + Sync + 'static>> {
    let s = s.trim();
    if s.is_empty() {
        Err("Expected `-` or `+`, got an empty string")?
    }
    let (prefix, namespace) = {
        let f = |&c: &char| matches!(c, '+' | '-' | '~' | '!');
        (
            s.chars().take_while(f).into_iter().collect::<String>(),
            s.chars().skip_while(f).into_iter().collect::<String>(),
        )
    };
    let kind = match &prefix[..] {
        "+" => InclusionKind::Included(DepsKind::Transitive),
        "+~" => InclusionKind::Included(DepsKind::Shallow),
        "+!" => InclusionKind::Included(DepsKind::None),
        "-" => InclusionKind::Excluded,
        prefix => Err(format!(
            "Expected `-`, `+~`, `+!` or `-`, got an `{prefix}`"
        ))?,
    };
    Ok(InclusionClause {
        kind,
        namespace: namespace.to_string().into(),
    })
}

#[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
pub struct TranslationOptions {
    /// Space-separated list of inclusion clauses. An inclusion clause
    /// is a Rust path prefixed with `+`, `+~`, `+!` or `-`. `-`
    /// excludes any matched item, `+` includes any matched item and
    /// their dependencies, `+~` includes any matched item and their
    /// direct dependencies, `+!` includes any matched item strictly
    /// (without including dependencies). By default, every item is
    /// included. Rust path chunks can be either a concrete string, or
    /// a glob (just like bash globs, but with Rust paths).
    #[arg(
        value_parser = parse_inclusion_clause,
        value_delimiter = ' ',
    )]
    #[arg(short, allow_hyphen_values(true))]
    include_namespaces: Vec<InclusionClause>,
}

#[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
pub struct BackendOptions {
    #[command(subcommand)]
    pub backend: Backend,

    /// Don't write anything on disk. Output everything as JSON to stdout
    /// instead.
    #[arg(long = "dry-run")]
    pub dry_run: bool,

    /// Verbose mode for the Hax engine. Set `-vv` for maximal verbosity.
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,

    /// Enable engine debugging: dumps the AST at each phase.
    ///
    /// The value of `<DEBUG_ENGINE>` can be either:
    ///
    ///  - `interactive` (or `i`): enables debugging of the engine,
    /// and visualize interactively in a webapp how a crate was
    /// transformed by each phase, both in Rust-like syntax and
    /// browsing directly the internal AST. By default, the webapp is
    /// hosted on `http://localhost:8000`, the port can be override by
    /// setting the `HAX_DEBUGGER_PORT` environment variable.
    ///
    /// - `<FILE>` or `file:<FILE>`: outputs the different AST as JSON
    /// to `<FILE>`. `<FILE>` can be either [-] or a path.
    #[arg(short, long = "debug-engine")]
    pub debug_engine: Option<DebugEngineMode>,

    #[command(flatten)]
    pub translation_options: TranslationOptions,
}

#[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
pub enum ExporterCommand {
    /// Translate to a backend. The translated modules will be written
    /// under the directory `<PKG>/proofs/<BACKEND>/extraction`, where
    /// `<PKG>` is the translated cargo package name and `<BACKEND>`
    /// the name of the backend.
    #[clap(name = "into")]
    Backend(BackendOptions),

    /// Export directly as a JSON file
    JSON {
        /// Path to the output JSON file, "-" denotes stdout.
        #[arg(
            short,
            long = "output-file",
            default_value = "hax_frontend_export.json"
        )]
        output_file: PathOrDash,
        /// Whether the bodies are exported as THIR, built MIR, const
        /// MIR, or a combination. Repeat this option to extract a
        /// combination (e.g. `-k thir -k mir-built`). Pass `--kind`
        /// alone with no value to disable body extraction.
        #[arg(
            value_enum,
            short,
            long = "kind",
            num_args = 0..=3,
            default_values_t = [ExportBodyKind::Thir]
        )]
        kind: Vec<ExportBodyKind>,

        /// Whether to include extra informations about `DefId`s.
        #[arg(short = 'E', long = "include-extra", default_value = "false")]
        include_extra: bool,
    },
}

#[derive(
    JsonSchema, ValueEnum, Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord,
)]
pub enum ExportBodyKind {
    Thir,
    MirBuilt,
    MirConst,
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
#[command(author, version = concat!("commit=", env!("HAX_GIT_COMMIT_HASH"), " ", "describe=", env!("HAX_GIT_DESCRIBE")), name = "hax", about, long_about = None)]
pub struct Options {
    /// Replace the expansion of each macro matching PATTERN by their
    /// invocation. PATTERN denotes a rust path (i.e. `A::B::c`) in
    /// which glob patterns are allowed. The glob pattern * matches
    /// any name, the glob pattern ** matches zero, one or more
    /// names. For instance, `A::B::C::D::X` and `A::E::F::D::Y`
    /// matches `A::**::D::*`.
    #[arg(
        short = 'i',
        long = "inline-macro-call",
        value_name = "PATTERN",
        value_parser,
        value_delimiter = ',',
        default_values = [
            "hacspec_lib::array::array", "hacspec_lib::array::public_bytes", "hacspec_lib::array::bytes",
            "hacspec_lib::math_integers::public_nat_mod", "hacspec_lib::math_integers::unsigned_public_integer",
        ],
    )]
    pub inline_macro_calls: Vec<Namespace>,

    /// Semi-colon terminated list of arguments to pass to the
    /// `cargo build` invocation. For example, to apply this
    /// program on a package `foo`, use `-C -p foo ;`. (make sure
    /// to escape `;` correctly in your shell)
    #[arg(default_values = Vec::<&str>::new(), short='C', allow_hyphen_values=true, num_args=1.., long="cargo-args", value_terminator=";")]
    pub cargo_flags: Vec<String>,

    #[command(subcommand)]
    pub command: Option<Command>,

    /// `cargo` caching is disabled by default, this flag enables it back.
    #[arg(long="enable-cargo-cache", action=clap::builder::ArgAction::SetTrue)]
    pub force_cargo_build: ForceCargoBuild,

    /// Apply the command to every local package of the dependency closure. By
    /// default, the command is only applied to the primary packages (i.e. the
    /// package(s) of the current directory, or the ones selected with cargo
    /// options like `-C -p <PKG> ;`).
    #[arg(long = "deps")]
    pub deps: bool,
}

impl NormalizePaths for ExporterCommand {
    fn normalize_paths(&mut self) {
        use ExporterCommand::*;
        match self {
            JSON { output_file, .. } => output_file.normalize_paths(),
            _ => (),
        }
    }
}

impl NormalizePaths for Command {
    fn normalize_paths(&mut self) {
        match self {
            Command::ExporterCommand(cmd) => cmd.normalize_paths(),
            _ => (),
        }
    }
}
impl NormalizePaths for Options {
    fn normalize_paths(&mut self) {
        if let Some(c) = &mut self.command {
            c.normalize_paths()
        }
    }
}

impl From<Options> for hax_frontend_exporter_options::Options {
    fn from(opts: Options) -> hax_frontend_exporter_options::Options {
        hax_frontend_exporter_options::Options {
            inline_macro_calls: opts.inline_macro_calls,
        }
    }
}

pub const ENV_VAR_OPTIONS_FRONTEND: &str = "DRIVER_HAX_FRONTEND_OPTS";
