// There's a conflict between `mir::ScalarInt`and `todo::ScalarInt` but it doesn't matter.
#![allow(ambiguous_glob_reexports)]

mod copied;
mod def_id;
mod index;
mod mir;
#[cfg(feature = "full")]
mod mir_traits;
mod new;
mod replaced;
mod todo;

pub use copied::*;
pub use def_id::*;
pub use index::*;
pub use mir::*;
#[cfg(feature = "full")]
pub use mir_traits::*;
pub use new::*;
pub use replaced::*;
pub use todo::*;
