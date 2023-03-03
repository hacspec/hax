use clap::Parser;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NamespaceChunk {
    GlobOne,  // *
    GlobMany, // **
    Exact(String),
}

impl std::convert::From<&str> for NamespaceChunk {
    fn from(s: &str) -> Self {
        match s {
            "*" => NamespaceChunk::GlobOne,
            "**" => NamespaceChunk::GlobMany,
            _ => NamespaceChunk::Exact(String::from(s)),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Namespace(pub Vec<NamespaceChunk>);

impl std::convert::From<String> for Namespace {
    fn from(s: String) -> Self {
        Namespace(
            s.split("::")
                .into_iter()
                .filter(|s| s.len() > 0)
                .map(|s| NamespaceChunk::from(s))
                .collect(),
        )
    }
}

impl Namespace {
    pub fn matches(&self, path: &Vec<String>) -> bool {
        fn aux(pattern: &[NamespaceChunk], path: &[String]) -> bool {
            use NamespaceChunk::*;
            match (pattern, path) {
                ([], []) => true,
                ([Exact(x), pattern @ ..], [y, path @ ..]) => x == y && aux(pattern, path),
                ([GlobOne, pattern @ ..], [_, path @ ..]) => aux(pattern, path),
                ([GlobMany, pattern @ ..], []) => aux(pattern, path),
                ([GlobMany, pattern_tl @ ..], [path_hd, path_tl @ ..]) => {
                    aux(pattern_tl, path) || aux(pattern, path_tl)
                }
                _ => false,
            }
        }
        aux(self.0.as_slice(), path.as_slice())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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
            PathOrDash::Dash => box std::io::stdout(),
            PathOrDash::Path(path) => box std::fs::File::create(&path).unwrap(),
        }
    }
    pub fn map_path<F: FnOnce(&Path) -> PathBuf>(&self, f: F) -> Self {
        match self {
            PathOrDash::Path(path) => PathOrDash::Path(f(path)),
            PathOrDash::Dash => PathOrDash::Dash,
        }
    }
}

#[derive(Parser, Debug, Clone, Serialize, Deserialize)]
#[command(author, version, about, long_about = None)]
pub struct Options {
    /// Path to the output JSON file, "-" denotes stdout.
    #[arg(short, long = "output-file", default_value = "thir_export.json")]
    pub output_file: PathOrDash,

    /// Replace the expansion of each macro matching PATTERN by their
    /// invokation. PATTERN denotes a rust path (i.e. [A::B::c]) in
    /// which glob patterns are allowed. The glob pattern * matches
    /// any name, the glob pattern ** matches zero, one or more
    /// names. For instance, [A::B::C::D::X] and [A::E::F::D::Y]
    /// matches [A::**::D::*].
    #[arg(
        long = "inline-macro-call",
        value_name = "PATTERN",
        value_parser,
        value_delimiter = ','
    )]
    pub inline_macro_calls: Vec<Namespace>,

    /// Export JSON schema in FILE.
    #[arg(long = "export-json-schema")]
    pub export_json_schema: Option<PathOrDash>,

    /// Arguments to pass to the `cargo build` invokation made by
    /// `thir-export`. For example, to export the THIR of a package
    /// `foo`, use `-p foo`.
    #[arg(default_values = Vec::<&str>::new(), last = true)]
    pub cargo_flags: Vec<String>,
}
