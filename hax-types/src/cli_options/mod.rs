use crate::prelude::*;

use clap::{Parser, Subcommand, ValueEnum};
use std::fmt;

pub use hax_frontend_exporter_options::*;
pub mod extension;
use extension::Extension;

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
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

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone, Default)]
pub struct ForceCargoBuild {
    pub data: u64,
}

impl std::convert::From<&str> for ForceCargoBuild {
    fn from(s: &str) -> Self {
        use std::time::{SystemTime, UNIX_EPOCH};
        if s == "false" {
            let data = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|r| r.as_millis())
                .unwrap_or(0);
            ForceCargoBuild { data: data as u64 }
        } else {
            ForceCargoBuild::default()
        }
    }
}

#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema)]
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

#[derive_group(Serializers)]
#[derive(JsonSchema, Parser, Debug, Clone)]
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
    pub assume_items: Vec<InclusionClause>,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Parser, Debug, Clone)]
pub struct FStarOptions<E: Extension> {
    /// Set the Z3 per-query resource limit
    #[arg(long, default_value = "15")]
    pub z3rlimit: u32,
    /// Number of unrolling of recursive functions to try
    #[arg(long, default_value = "0")]
    pub fuel: u32,
    /// Number of unrolling of inductive datatypes to try
    #[arg(long, default_value = "1")]
    pub ifuel: u32,
    /// Modules for which Hax should extract interfaces (`*.fsti`
    /// files) in supplement to implementations (`*.fst` files). By
    /// default we extract no interface, only implementations. If a
    /// item is signature only (see the `+:` prefix of the
    /// `--include_namespaces` flag of the `into` subcommand), then
    /// its namespace is extracted with an interface. This flag
    /// expects a space-separated list of inclusion clauses. An
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
    pub interfaces: Vec<InclusionClause>,

    #[arg(long, default_value = "100", env = "HAX_FSTAR_LINE_WIDTH")]
    pub line_width: u16,

    #[group(flatten)]
    pub cli_extension: E::FStarOptions,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Subcommand, Debug, Clone)]
pub enum Backend<E: Extension> {
    /// Use the F* backend
    Fstar(FStarOptions<E>),
    /// Use the Coq backend
    Coq,
    /// Use the SSProve backend
    Ssprove,
    /// Use the EasyCrypt backend (warning: work in progress!)
    Easycrypt,
    /// Use the ProVerif backend (warning: work in progress!)
    ProVerif(ProVerifOptions),
    /// Use the OCaml backend (warning: work in progress!)
    Ocaml,
}

impl fmt::Display for Backend<()> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Backend::Fstar(..) => write!(f, "fstar"),
            Backend::Coq => write!(f, "coq"),
            Backend::Ssprove => write!(f, "ssprove"),
            Backend::Easycrypt => write!(f, "easycrypt"),
            Backend::ProVerif(..) => write!(f, "proverif"),
            Backend::Ocaml => write!(f, "ocaml"),
        }
    }
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub enum DepsKind {
    Transitive,
    Shallow,
    None,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub enum InclusionKind {
    /// `+query` include the items selected by `query`
    Included(DepsKind),
    SignatureOnly,
    Excluded,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct InclusionClause {
    pub kind: InclusionKind,
    pub namespace: Namespace,
}

const PREFIX_INCLUDED_TRANSITIVE: &str = "+";
const PREFIX_INCLUDED_SHALLOW: &str = "+~";
const PREFIX_INCLUDED_NONE: &str = "+!";
const PREFIX_SIGNATURE_ONLY: &str = "+:";
const PREFIX_EXCLUDED: &str = "-";

impl ToString for InclusionClause {
    fn to_string(&self) -> String {
        let kind = match self.kind {
            InclusionKind::Included(DepsKind::Transitive) => PREFIX_INCLUDED_TRANSITIVE,
            InclusionKind::Included(DepsKind::Shallow) => PREFIX_INCLUDED_SHALLOW,
            InclusionKind::Included(DepsKind::None) => PREFIX_INCLUDED_NONE,
            InclusionKind::SignatureOnly => PREFIX_SIGNATURE_ONLY,
            InclusionKind::Excluded => PREFIX_EXCLUDED,
        };
        format!("{kind}{}", self.namespace.to_string())
    }
}

pub fn parse_inclusion_clause(
    s: &str,
) -> Result<InclusionClause, Box<dyn std::error::Error + Send + Sync + 'static>> {
    let s = s.trim();
    if s.is_empty() {
        Err("Expected `-` or `+`, got an empty string")?
    }
    let (prefix, namespace) = {
        let f = |&c: &char| matches!(c, '+' | '-' | '~' | '!' | ':');
        (
            s.chars().take_while(f).into_iter().collect::<String>(),
            s.chars().skip_while(f).into_iter().collect::<String>(),
        )
    };
    let kind = match &prefix[..] {
        PREFIX_INCLUDED_TRANSITIVE => InclusionKind::Included(DepsKind::Transitive),
        PREFIX_INCLUDED_SHALLOW => InclusionKind::Included(DepsKind::Shallow),
        PREFIX_INCLUDED_NONE => InclusionKind::Included(DepsKind::None),
        PREFIX_SIGNATURE_ONLY => InclusionKind::SignatureOnly,
        PREFIX_EXCLUDED => InclusionKind::Excluded,
        prefix => Err(format!(
            "Expected `+`, `+~`, `+!`, `+:` or `-`, got an `{prefix}`"
        ))?,
    };
    Ok(InclusionClause {
        kind,
        namespace: namespace.to_string().into(),
    })
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Parser, Debug, Clone)]
pub struct TranslationOptions {
    /// Controls which Rust item should be extracted or not.
    ///
    /// This is a space-separated list of patterns prefixed with a
    /// modifier, read from the left to the right.
    ///
    /// A pattern is a Rust path (say `mycrate::mymod::myfn`) where
    /// globs are allowed: `*` matches any name
    /// (e.g. `mycrate::mymod::myfn` is matched by
    /// `mycrate::*::myfn`), while `**` matches any subpath, empty
    /// included (e.g. `mycrate::mymod::myfn` is matched by
    /// `**::myfn`).

    /// By default, hax includes all items. Then, the patterns
    /// prefixed by modifiers are processed from left to right,
    /// excluding or including items. Each pattern selects a number of
    /// item. The modifiers are:

    /// {n}{n} - `+`: includes the selected items with their
    /// dependencies, transitively (e.g. if function `f` calls `g`
    /// which in turn calls `h`, then `+k::f` includes `f`, `g` and
    /// `h`)

    /// {n} - `+~`: includes the selected items with their direct
    /// dependencies only (following the previous example, `+~k::f`
    /// would select `f` and `g`, but not `h`)

    /// {n} - `+!`: includes the selected items, without their
    /// dependencies (`+!k::f` would only select `f`)

    /// {n} - `+:`: only includes the type of the selected items (no
    /// dependencies). This includes full struct and enums, but only
    /// the type signature of functions and trait impls (except when
    /// they contain associated types), dropping their bodies.
    #[arg(
        value_parser = parse_inclusion_clause,
        value_delimiter = ' ',
    )]
    #[arg(short, allow_hyphen_values(true))]
    pub include_namespaces: Vec<InclusionClause>,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Parser, Debug, Clone)]
pub struct BackendOptions<E: Extension> {
    #[command(subcommand)]
    pub backend: Backend<E>,

    /// Don't write anything on disk. Output everything as JSON to stdout
    /// instead.
    #[arg(long = "dry-run")]
    pub dry_run: bool,

    /// Verbose mode for the Hax engine. Set `-vv` for maximal verbosity.
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,

    /// Prints statistics about how many items have been translated
    /// successfully by the engine.
    #[arg(long)]
    pub stats: bool,

    /// Enables profiling for the engine: for each phase of the
    /// engine, time and memory usage are recorded and reported.
    #[arg(long)]
    pub profile: bool,

    /// Enable engine debugging: dumps the AST at each phase.
    ///
    /// The value of `<DEBUG_ENGINE>` can be either:

    /// {n}{n} - `interactive` (or `i`): enables debugging of the engine,
    /// and visualize interactively in a webapp how a crate was
    /// transformed by each phase, both in Rust-like syntax and
    /// browsing directly the internal AST. By default, the webapp is
    /// hosted on `http://localhost:8000`, the port can be override by
    /// setting the `HAX_DEBUGGER_PORT` environment variable.

    /// {n} - `<FILE>` or `file:<FILE>`: outputs the different AST as JSON
    /// to `<FILE>`. `<FILE>` can be either [-] or a path.
    #[arg(short, long = "debug-engine")]
    pub debug_engine: Option<DebugEngineMode>,

    /// Extract type aliases. This is disabled by default, since
    /// extracted terms depends on expanded types rather than on type
    /// aliases. Turning this option on is discouraged: Rust type
    /// synonyms can ommit generic bounds, which are ususally
    /// necessary in the hax backends, leading to typechecking
    /// errors. For more details see
    /// https://github.com/hacspec/hax/issues/708.
    #[arg(long)]
    pub extract_type_aliases: bool,

    #[command(flatten)]
    pub translation_options: TranslationOptions,

    /// Where to put the output files resulting from the translation.
    /// Defaults to "<crate folder>/proofs/<backend>/extraction".
    #[arg(long)]
    pub output_dir: Option<PathBuf>,

    #[group(flatten)]
    pub cli_extension: E::BackendOptions,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Subcommand, Debug, Clone)]
pub enum Command<E: Extension> {
    /// Translate to a backend. The translated modules will be written
    /// under the directory `<PKG>/proofs/<BACKEND>/extraction`, where
    /// `<PKG>` is the translated cargo package name and `<BACKEND>`
    /// the name of the backend.
    #[clap(name = "into")]
    Backend(BackendOptions<E>),

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

        /// By default, `cargo hax json` outputs a JSON where every
        /// piece of information is inlined. This however creates very
        /// large JSON files. This flag enables the use of unique IDs
        /// and outputs a map from IDs to actual objects.
        #[arg(long)]
        use_ids: bool,

        /// Whether to include extra informations about `DefId`s.
        #[arg(short = 'E', long = "include-extra", default_value = "false")]
        include_extra: bool,
    },

    #[command(flatten)]
    CliExtension(E::Command),
}

impl<E: Extension> Command<E> {
    pub fn body_kinds(&self) -> Vec<ExportBodyKind> {
        match self {
            Command::JSON { kind, .. } => kind.clone(),
            _ => vec![ExportBodyKind::Thir],
        }
    }
}

#[derive_group(Serializers)]
#[derive(JsonSchema, ValueEnum, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExportBodyKind {
    Thir,
    MirBuilt,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Parser, Debug, Clone)]
#[command(
    author,
    version = crate::HAX_VERSION,
    long_version = concat!("\nversion=", env!("HAX_VERSION"), "\n", "commit=", env!("HAX_GIT_COMMIT_HASH")),
    name = "hax",
    about,
    long_about = None
)]
pub struct ExtensibleOptions<E: Extension> {
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
    pub command: Command<E>,

    /// `cargo` caching is enable by default, this flag disables it.
    #[arg(long="disable-cargo-cache", action=clap::builder::ArgAction::SetFalse)]
    pub force_cargo_build: ForceCargoBuild,

    /// Apply the command to every local package of the dependency closure. By
    /// default, the command is only applied to the primary packages (i.e. the
    /// package(s) of the current directory, or the ones selected with cargo
    /// options like `-C -p <PKG> ;`).
    #[arg(long = "deps")]
    pub deps: bool,

    /// By default, hax uses `$CARGO_TARGET_DIR/hax` as target folder,
    /// to avoid recompilation when working both with `cargo hax` and
    /// `cargo build` (or, e.g. `rust-analyzer`). This option disables
    /// this behavior.
    #[arg(long)]
    pub no_custom_target_directory: bool,

    /// Diagnostic format. Sets `cargo`'s `--message-format` as well,
    /// if not present.
    #[arg(long, default_value = "human")]
    pub message_format: MessageFormat,

    #[group(flatten)]
    pub extension: E::Options,
}

pub type Options = ExtensibleOptions<()>;

#[derive_group(Serializers)]
#[derive(JsonSchema, ValueEnum, Debug, Clone, Copy, Eq, PartialEq)]
pub enum MessageFormat {
    Human,
    Json,
}

impl<E: Extension> NormalizePaths for Command<E> {
    fn normalize_paths(&mut self) {
        use Command::*;
        match self {
            JSON { output_file, .. } => output_file.normalize_paths(),
            _ => (),
        }
    }
}

impl NormalizePaths for Options {
    fn normalize_paths(&mut self) {
        self.command.normalize_paths()
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
