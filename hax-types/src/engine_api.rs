use crate::cli_options::*;
use crate::prelude::*;

type ThirBody = hax_frontend_exporter::ThirBody;

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct EngineOptions {
    pub backend: BackendOptions,
    pub input: Vec<hax_frontend_exporter::Item<ThirBody>>,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct File {
    pub path: String,
    pub contents: String,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct Output {
    pub diagnostics: Vec<crate::diagnostics::Diagnostics>,
    pub files: Vec<File>,
    pub debug_json: Option<String>,
}

pub mod protocol {
    use super::*;
    #[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
    pub enum FromEngine {
        Diagnostic(crate::diagnostics::Diagnostics),
        File(File),
        Exit,
        Ping,
    }
    #[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
    pub enum ToEngine {
        Pong,
    }
}

// This is located here for dependency reason, but this is not related
// to the engine (yet?).
#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize)]
pub struct WithDefIds<Body: hax_frontend_exporter::IsBody> {
    pub def_ids: Vec<hax_frontend_exporter::DefId>,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    pub items: Vec<hax_frontend_exporter::Item<Body>>,
}
