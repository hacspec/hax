#[cfg(feature = "macros")]
pub use crate::proc_macros::*;

#[macro_export]
macro_rules! debug_assert {
    ($($arg:tt)*) => {
        ::core::debug_assert!($($arg)*);
    };
}

#[macro_export]
macro_rules! assert {
    ($($arg:tt)*) => {
        ::core::assert!($arg);
    };
}

#[macro_export]
macro_rules! assume {
    ($formula:expr) => {
        ()
    };
}

pub fn forall<T>(_f: impl Fn(T) -> bool) -> bool {
    true
}

pub fn exists<T>(_f: impl Fn(T) -> bool) -> bool {
    true
}

pub fn implies(lhs: bool, rhs: impl Fn() -> bool) -> bool {
    !lhs || rhs()
}
