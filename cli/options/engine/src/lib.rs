use hax_cli_options::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

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
    pub diagnostics: Vec<hax_diagnostics::Diagnostics>,
    pub files: Vec<File>,
    pub debug_json: Option<String>,
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

pub const HAX_DRIVER_STDERR_PREFIX: &str = "::hax-driver::";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmitHaxMetaMessage {
    pub working_dir: PathBuf,
    pub manifest_dir: PathBuf,
    pub path: PathBuf,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HaxDriverMessage {
    EmitHaxMeta(EmitHaxMetaMessage),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HaxMeta<Body: hax_frontend_exporter::IsBody> {
    pub crate_name: String,
    pub crate_type: String,
    pub cg_metadata: String,
    pub externs: Vec<PathBuf>,
    pub items: Vec<hax_frontend_exporter::Item<Body>>,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    pub def_ids: Vec<hax_frontend_exporter::DefId>,
}

#[macro_export]
macro_rules! with_kind_type {
    ($kind:expr, <$t:ident>|| $body:expr) => {{
        mod from {
            pub use hax_cli_options::ExportBodyKind::{MirBuilt as MB, Thir as T};
        }
        mod to {
            pub type T = hax_frontend_exporter::ThirBody;
            pub type MB = hax_frontend_exporter::MirBody<hax_frontend_exporter::mir_kinds::Built>;
        }
        let mut kind: Vec<hax_cli_options::ExportBodyKind> = $kind;
        kind.sort();
        kind.dedup();
        match kind.as_slice() {
            [from::MB] => {
                type $t = to::MB;
                $body
            }
            [from::T] => {
                type $t = to::T;
                $body
            }
            [from::T, from::MB] => {
                type $t = (to::MB, to::T);
                $body
            }
            [] => {
                type $t = ();
                $body
            }
            _ => panic!("Unsupported kind {:#?}", kind),
        }
    }};
}
