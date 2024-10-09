use crate::cli_options::*;
use crate::prelude::*;

type ThirBody = hax_frontend_exporter::ThirBody;

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct EngineOptions {
    pub backend: BackendOptions<()>,
    pub input: Vec<hax_frontend_exporter::Item<ThirBody>>,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct File {
    pub path: String,
    pub contents: String,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct Output {
    pub diagnostics: Vec<crate::diagnostics::Diagnostics>,
    pub files: Vec<File>,
    pub debug_json: Option<String>,
}

pub mod protocol {
    use super::*;
    #[derive_group(Serializers)]
    #[derive(JsonSchema, Debug, Clone)]
    pub enum FromEngine {
        Diagnostic(crate::diagnostics::Diagnostics),
        File(File),
        PrettyPrintDiagnostic(crate::diagnostics::Diagnostics),
        PrettyPrintRust(String),
        DebugString(String),
        Exit,
        Ping,
    }
    #[derive_group(Serializers)]
    #[derive(JsonSchema, Debug, Clone)]
    pub enum ToEngine {
        PrettyPrintedDiagnostic(String),
        PrettyPrintedRust(Result<String, String>),
        Pong,
    }
}

// This is located here for dependency reason, but this is not related
// to the engine (yet?).
#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct WithDefIds<Body: hax_frontend_exporter::IsBody> {
    pub def_ids: Vec<hax_frontend_exporter::DefId>,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    pub items: Vec<hax_frontend_exporter::Item<Body>>,
    pub comments: Vec<(hax_frontend_exporter::Span, String)>,
}
