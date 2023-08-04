#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(concat_idents)]
#![feature(trait_alias)]
#![feature(type_changing_struct_update)]
#![feature(macro_metavar_expr)]
#![feature(if_let_guard)]
#![feature(let_chains)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unreachable_code)]
#![allow(dead_code)]
#![allow(incomplete_features)]
#![feature(specialization)]

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

mod body;
mod constant_utils;
mod rustc_utils;
pub mod state;
mod types;

mod index_vec;
mod prelude;

pub use prelude::{
    argument_span_of_mac_call, inline_macro_invocations, mir_kinds, translate_span, IsBody, Item,
    MirBody, Span, ThirBody,
};

mod sinto;
mod utils;

pub use adt_into::AdtInto;
pub use sinto::SInto;
