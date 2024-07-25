use crate::cli_options::Backend;
use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema)]
pub enum HaxMessage {
    Diagnostic {
        diagnostic: super::Diagnostics,
        working_dir: PathBuf,
    },
    EngineNotFound {
        is_opam_setup_correctly: bool,
    },
    WroteFile {
        path: PathBuf,
    },
    HaxEngineFailure {
        exit_code: i32,
    },
    CargoBuildFailure,
    WarnExperimentalBackend {
        backend: Backend,
    },
}
