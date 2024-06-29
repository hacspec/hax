use crate::prelude::*;

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
            pub use hax_types::cli_options::ExportBodyKind::{MirBuilt as MB, Thir as T};
        }
        mod to {
            pub type T = hax_frontend_exporter::ThirBody;
            pub type MB = hax_frontend_exporter::MirBody<hax_frontend_exporter::mir_kinds::Built>;
        }
        let mut kind: Vec<::hax_types::cli_options::ExportBodyKind> = $kind;
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
pub use with_kind_type;
