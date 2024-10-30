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
#[allow(non_snake_case)]
#[derive(JsonSchema, Debug, Clone)]
pub struct SourceMap {
    pub mappings: String,
    pub sourceRoot: String,
    pub sources: Vec<String>,
    pub sourcesContent: Vec<Option<String>>,
    pub names: Vec<String>,
    pub version: u8,
    pub file: String,
}

impl SourceMap {
    pub fn inline_sources_content(&mut self) {
        self.sourcesContent = vec![];
        for source in &self.sources {
            let path = if self.sourceRoot.is_empty() {
                source.clone()
            } else {
                format!("{}/{}", &self.sourceRoot, source)
            };
            let contents = Some(std::fs::read_to_string(path).unwrap());
            self.sourcesContent.push(contents);
        }
    }
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct File {
    pub path: String,
    pub contents: String,
    pub sourcemap: Option<SourceMap>,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct Output {
    pub diagnostics: Vec<crate::diagnostics::Diagnostics>,
    pub files: Vec<File>,
    pub debug_json: Option<String>,
}

#[derive_group(Serializers)]
#[derive(JsonSchema, Debug, Clone)]
pub struct ProfilingData {
    /// What context are we profiling?
    pub context: String,
    /// How long this took?
    pub time_ns: u64,
    /// How much memory this took? This is using OCaml's
    /// `Gc.minor_words`, and is probably not very precise.
    pub memory: u64,
    /// How many things were processed? (often, this is the number of
    /// items a phase processes)
    pub quantity: u32,
    /// Did the action errored? This is important since a failed
    /// action might have exited very early, making the numbers
    /// unusable.
    pub errored: bool,
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
        ProfilingData(ProfilingData),
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
