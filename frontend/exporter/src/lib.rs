#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(concat_idents)]
#![feature(trait_alias)]
#![feature(type_changing_struct_update)]
#![feature(macro_metavar_expr)]
#![feature(if_let_guard)]
#![feature(let_chains)]
#![allow(incomplete_features)]
#![feature(specialization)]
#![feature(return_position_impl_trait_in_trait)]
#![allow(rustdoc::private_intra_doc_links)]

cfg_if::cfg_if! {
    if #[cfg(feature = "full")] {
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
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "full")] {
        mod deterministic_hash;
        mod rustc_utils;
        mod utils;

        pub mod state;
        pub use sinto::SInto;
    }
}

mod body;
mod constant_utils;
mod index_vec;
mod prelude;
mod sinto;
mod traits;
mod types;

pub use hax_adt_into::AdtInto;
pub use hax_frontend_exporter_options as options;
pub use prelude::*;
