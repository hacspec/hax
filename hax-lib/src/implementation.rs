mod abstraction;
pub use abstraction::*;

mod int;
pub use int::*;

mod prop;
pub use prop::*;

#[cfg(feature = "macros")]
pub use crate::proc_macros::*;

#[doc(hidden)]
#[cfg(hax)]
#[macro_export]
macro_rules! proxy_macro_if_not_hax {
    ($macro:path, no, $($arg:tt)*) => {
        ()
    };
    ($macro:path, $f:expr, $cond:expr$(, $($arg:tt)*)?) => {
        $f($cond)
    };
}

#[cfg(not(debug_assertions))]
#[doc(hidden)]
#[cfg(not(hax))]
#[macro_export]
macro_rules! proxy_macro_if_not_hax {
    ($macro:path, $f:expr, $($arg:tt)*) => {};
}

#[cfg(debug_assertions)]
#[doc(hidden)]
#[cfg(not(hax))]
#[macro_export]
macro_rules! proxy_macro_if_not_hax {
    ($macro:path, $f:expr, $($arg:tt)*) => {
        $macro!($($arg)*)
    };
}

#[macro_export]
/// Proxy to `std::debug_assert!`. Compiled with `hax`, this
/// disappears.
macro_rules! debug_assert {
    ($($arg:tt)*) => {
        $crate::proxy_macro_if_not_hax!(::core::debug_assert, no, $($arg)*)
    };
}

#[macro_export]
/// Proxy to `std::assert!`. Compiled with `hax`, this is transformed
/// into a `assert` in the backend.
macro_rules! assert {
    ($($arg:tt)*) => {
        $crate::proxy_macro_if_not_hax!(::core::assert, $crate::assert, $($arg)*)
    };
}

#[doc(hidden)]
#[cfg(hax)]
/// This function exists only when compiled with `hax`, and is not
/// meant to be used directly. It is called by `assert!` only in
/// appropriate situations.
pub fn assert(_formula: Prop) {}

#[doc(hidden)]
#[cfg(hax)]
/// This function exists only when compiled with `hax`, and is not
/// meant to be used directly. It is called by `assume!` only in
/// appropriate situations.
pub fn assume(_formula: Prop) {}

#[cfg(hax)]
#[macro_export]
macro_rules! assume {
    ($formula:expr) => {
        $crate::assume($formula)
    };
}

/// Assume a boolean formula holds. In Rust, this is expanded to the
/// expression `()`. While extracted with Hax, this gets expanded to a
/// call to an `assume` function.
///
/// # Example:
///
/// ```rust
/// fn sum(x: u32, y: u32) -> u32 {
///   hax_lib::assume!(x < 4242 && y < 424242);
///   x + y
/// }
/// ```
#[cfg(not(hax))]
#[macro_export]
macro_rules! assume {
    ($formula:expr) => {
        ()
    };
}


/// Dummy function that carries a string to be printed as such in the output language
#[doc(hidden)]
pub fn inline(_: &str) {}

/// Similar to `inline`, but allows for any type. Do not use directly.
#[doc(hidden)]
pub fn inline_unsafe<T>(_: &str) -> T {
    unreachable!()
}

/// A dummy function that holds a loop invariant.
#[doc(hidden)]
pub fn _internal_loop_invariant<T, P: FnOnce(T) -> Prop>(_: P) {}

/// A type that implements `Refinement` should be a newtype for a
/// type `T`. The field holding the value of type `T` should be
/// private, and `Refinement` should be the only interface to the
/// type.
///
/// Please never implement this trait yourself, use the
/// `refinement_type` macro instead.
pub trait Refinement {
    /// The base type
    type InnerType;
    /// Smart constructor capturing an invariant. Its extraction will
    /// yield a proof obligation.
    fn new(x: Self::InnerType) -> Self;
    /// Destructor for the refined type
    fn get(self) -> Self::InnerType;
    /// Gets a mutable reference to a refinement
    fn get_mut(&mut self) -> &mut Self::InnerType;
    /// Tests wether a value satisfies the refinement
    fn invariant(value: Self::InnerType) -> Prop;
}

/// A utilitary trait that provides a `into_checked` method on traits
/// that have a refined counter part. This trait is parametrized by a
/// type `Target`: a base type can be refined in multiple ways.
///
/// Please never implement this trait yourself, use the
/// `refinement_type` macro instead.
pub trait RefineAs<RefinedType> {
    /// Smart constructor for `RefinedType`, checking the invariant
    /// `RefinedType::invariant`. The check is done statically via
    /// extraction to hax: extracted code will yield static proof
    /// obligations.
    ///
    /// In addition, in debug mode, the invariant is checked at
    /// run-time, unless this behavior was disabled when defining the
    /// refinement type `RefinedType` with the `refinement_type` macro
    /// and its `no_debug_runtime_check` option.
    fn into_checked(self) -> RefinedType;
}
