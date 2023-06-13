#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(concat_idents)]
#![feature(trait_alias)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unreachable_code)]
#![allow(dead_code)]
#![feature(macro_metavar_expr)]

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
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

mod all;
mod items;
mod manual;
mod sinto;
pub mod state;
pub mod utils;

pub use adt_into::AdtInto;
pub use sinto::SInto;

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub use all::*;
pub use items::*;
pub use state::*;

// #[derive(AdtInto, Clone, Debug, Serialize, Deserialize, JsonSchema)]
// #[args(<S>, from: rustc_hir::Movability, state: S as state)]
// pub enum Movability {
//     Static,
//     Movable,
// }
