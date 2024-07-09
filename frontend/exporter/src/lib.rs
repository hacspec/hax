#![feature(trait_alias)]
#![allow(rustdoc::private_intra_doc_links)]
#![cfg_attr(feature = "rustc", feature(type_changing_struct_update))]
#![cfg_attr(feature = "rustc", feature(macro_metavar_expr))]
#![cfg_attr(feature = "rustc", feature(concat_idents))]
#![cfg_attr(feature = "rustc", feature(rustc_private))]

macro_rules! cfg_feature_rustc {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "rustc")]
            $item
        )*
    }
}

cfg_feature_rustc! {
    // When the feature `rustc` is enabled, we enable the bridges
    // between rustc ASTs, which are defined in the crates
    // `rustc_*`. We thus need to import them with `extern crate
    // rustc_*`
    extern crate rustc_abi;
    extern crate rustc_ast;
    extern crate rustc_ast_pretty;
    extern crate rustc_data_structures;
    extern crate rustc_driver;
    extern crate rustc_errors;
    extern crate rustc_hir;
    extern crate rustc_hir_analysis;
    extern crate rustc_index;
    extern crate rustc_infer;
    extern crate rustc_interface;
    extern crate rustc_middle;
    extern crate rustc_mir_build;
    extern crate rustc_session;
    extern crate rustc_span;
    extern crate rustc_target;
    extern crate rustc_trait_selection;
    extern crate rustc_type_ir;

    mod rustc_utils;
    pub mod state;
    mod utils;
    mod deterministic_hash;
}

mod body;
mod constant_utils;
mod types;

mod index_vec;
mod prelude;

pub use hax_frontend_exporter_options as options;
pub use prelude::*;

mod sinto;
mod traits;

pub use hax_adt_into::AdtInto;
pub use sinto::SInto;
