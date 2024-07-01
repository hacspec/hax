use crate::prelude::*;

pub const HAX_DRIVER_STDERR_PREFIX: &str = "::hax-driver::";

#[derive_group(Serializers)]
#[derive(Debug, Clone)]
pub struct EmitHaxMetaMessage {
    pub working_dir: PathBuf,
    pub manifest_dir: PathBuf,
    pub path: PathBuf,
}
#[derive_group(Serializers)]
#[derive(Debug, Clone)]
pub enum HaxDriverMessage {
    EmitHaxMeta(EmitHaxMetaMessage),
}

#[derive_group(Serializers)]
#[derive(Debug, Clone)]
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

impl<Body: hax_frontend_exporter::IsBody> HaxMeta<Body>
where
    Body: bincode::Encode + bincode::Decode,
{
    pub fn write(self, write: &mut impl std::io::Write) {
        let mut write = zstd::stream::write::Encoder::new(write, 0).unwrap();
        bincode::encode_into_std_write(self, &mut write, bincode::config::standard()).unwrap();
        write.finish().unwrap();
    }
    pub fn read(reader: impl std::io::Read) -> Self {
        let reader = zstd::stream::read::Decoder::new(reader).unwrap();
        let reader = std::io::BufReader::new(reader);
        bincode::decode_from_reader(reader, bincode::config::standard()).unwrap()
    }
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
