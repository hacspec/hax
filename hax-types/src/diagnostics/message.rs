use crate::cli_options::Backend;
use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Debug, Clone, JsonSchema)]
#[repr(u8)]
pub enum HaxMessage {
    Diagnostic {
        diagnostic: super::Diagnostics,
        working_dir: PathBuf,
    } = 254,
    EngineNotFound {
        is_opam_setup_correctly: bool,
    } = 0,
    ProducedFile {
        path: PathBuf,
        wrote: bool,
    } = 1,
    HaxEngineFailure {
        exit_code: i32,
    } = 2,
    CargoBuildFailure = 3,
    WarnExperimentalBackend {
        backend: Backend<()>,
    } = 4,
    ProfilingData(crate::engine_api::ProfilingData) = 5,
}

impl HaxMessage {
    // https://doc.rust-lang.org/reference/items/enumerations.html#pointer-casting
    pub fn discriminant(&self) -> u16 {
        unsafe { *(self as *const Self as *const u16) }
    }

    pub fn code(&self) -> String {
        match self {
            HaxMessage::Diagnostic { diagnostic, .. } => diagnostic.kind.code(),
            _ => format!("CARGOHAX{:0>4}", self.discriminant()),
        }
    }
}
