// Proc-macros must "reside in the root of the crate": whence the use
// of `std::include!` instead of proper module declaration.

#[cfg(feature = "hax")]
std::include!("implementation.rs");

#[cfg(not(feature = "hax"))]
std::include!("dummy.rs");
