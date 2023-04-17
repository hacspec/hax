use clap::{Parser, Subcommand};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

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

#[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
#[command(author, version, about, long_about = None)]
pub struct ForceCargoBuildCmd {
    /// [cargo] caching is disabled by default, this flag enables it back.
    #[arg(long="enable-cargo-cache", action=clap::builder::ArgAction::SetTrue)]
    pub force_cargo_build: ForceCargoBuild,
}

use circus_frontend_exporter::{Namespace, PathOrDash};

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

impl NormalizePaths for PathOrDash {
    fn normalize_paths(self) -> Self {
        match self {
            PathOrDash::Dash => PathOrDash::Dash,
            PathOrDash::Path(p) => PathOrDash::Path(absolute_path(p).unwrap()),
        }
    }
}

pub mod circus_frontend_part {
    use super::*;
    #[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
    #[command(author, version, about, long_about = None)]
    pub struct CircusFrontendBase {
        /// Replace the expansion of each macro matching PATTERN by their
        /// invokation. PATTERN denotes a rust path (i.e. [A::B::c]) in
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
        /// [cargo build] invokation. For example, to apply this
        /// program on a package [foo], use [-C -p foo;]. (make sure
        /// to escape [;] correctly in your shell)
        #[arg(default_values = Vec::<&str>::new(), short='C', allow_hyphen_values=true, num_args=1.., long="cargo-args", value_terminator=";")]
        pub cargo_flags: Vec<String>,
    }
    impl NormalizePaths for CircusFrontendBase {
        fn normalize_paths(self) -> Self {
            self
        }
    }

    #[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
    #[command(author, version, about, long_about = None)]
    pub struct Extra {
        /// Path to the output JSON file, "-" denotes stdout.
        #[arg(
            short,
            long = "output-file",
            default_value = "circus_frontend_export.json"
        )]
        pub output_file: PathOrDash,

        /// Export JSON schema in FILE.
        #[arg(long = "export-json-schema")]
        pub export_json_schema: Option<PathOrDash>,
    }

    impl NormalizePaths for Extra {
        fn normalize_paths(self) -> Self {
            Extra {
                output_file: self.output_file.normalize_paths(),
                export_json_schema: self.export_json_schema,
            }
        }
    }
    #[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
    #[command(author, version, about, long_about = None)]
    pub struct All {
        #[command(flatten)]
        pub extra: Extra,
        #[command(flatten)]
        pub base: CircusFrontendBase,
        #[command(flatten)]
        pub force_cargo_build: ForceCargoBuildCmd,
    }

    impl NormalizePaths for All {
        fn normalize_paths(self) -> Self {
            All {
                extra: self.extra.normalize_paths(),
                base: self.base,
                force_cargo_build: self.force_cargo_build,
            }
        }
    }

    impl Into<circus_frontend_exporter::Options> for All {
        fn into(self) -> circus_frontend_exporter::Options {
            circus_frontend_exporter::Options {
                export_json_schema: self.extra.export_json_schema,
                output_file: self.extra.output_file,
                cargo_flags: self.base.cargo_flags,
                inline_macro_calls: self.base.inline_macro_calls,
            }
        }
    }
}

pub mod circus_engine_part {
    use super::*;
    #[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
    pub enum Backend {
        /// Use the F* backend
        Fstar,
        /// Use the Coq backend
        Coq,
        /// Use the EasyCrypt backend
        EasyCrypt,
    }

    #[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
    pub struct Options {
        pub circus_frontend_exporter: circus_frontend_part::CircusFrontendBase,
        pub output_dir: std::path::PathBuf,
        pub backend: Backend,
    }
}

pub mod wrapped {
    use super::*;
    use circus_engine_part::*;

    #[derive(JsonSchema, Subcommand, Debug, Clone, Serialize, Deserialize)]
    pub enum JsonOrBackend {
        #[command(flatten)]
        Backend(Backend),

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

    #[derive(JsonSchema, Parser, Debug, Clone, Serialize, Deserialize)]
    #[command(author, version, about, long_about = None)]
    pub struct Options {
        #[command(flatten)]
        pub circus_frontend_exporter: circus_frontend_part::CircusFrontendBase,

        /// Directory in which the backend should output files.
        #[arg(short, long = "output-dir", default_value = "out/")]
        pub output_dir: std::path::PathBuf,

        #[command(subcommand)]
        pub backend: JsonOrBackend,

        #[command(flatten)]
        pub force_cargo_build: ForceCargoBuildCmd,
    }

    impl NormalizePaths for Options {
        fn normalize_paths(self) -> Self {
            Options {
                circus_frontend_exporter: self.circus_frontend_exporter.normalize_paths(),
                output_dir: absolute_path(self.output_dir).unwrap(),
                backend: self.backend,
                force_cargo_build: self.force_cargo_build,
            }
        }
    }
}
