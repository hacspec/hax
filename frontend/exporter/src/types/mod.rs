// There's a conflict between `mir::ScalarInt`and `todo::ScalarInt` but it doesn't matter.
#![allow(ambiguous_glob_reexports)]

mod def_id;
mod hir;
mod mir;
mod new;
pub(crate) mod serialize_int;
mod span;
mod thir;
mod ty;

pub use def_id::*;
pub use hir::*;
pub use mir::*;
pub use new::*;
pub use span::*;
pub use thir::*;
pub use ty::*;
