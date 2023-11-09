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
#[cfg(not(hax))]
#[macro_export]
macro_rules! proxy_macro_if_not_hax {
    ($macro:path, $f:expr, $($arg:tt)*) => {
        $macro!($($arg)*)
    };
}

#[macro_export]
macro_rules! debug_assert {
    ($($arg:tt)*) => {
        $crate::proxy_macro_if_not_hax!(::std::debug_assert, no, $($arg)*)
    };
}

#[macro_export]
macro_rules! assert {
    ($($arg:tt)*) => {
        $crate::proxy_macro_if_not_hax!(::std::assert, $crate::assert, $($arg)*)
    };
}

#[cfg(hax)]
pub fn assert(_formula: bool) {}

#[cfg(hax)]
pub fn assume(_formula: bool) {}

#[cfg(hax)]
#[macro_export]
macro_rules! assume {
    ($formula:expr) => {
        $crate::assume($formula)
    };
}
#[cfg(not(hax))]
#[macro_export]
macro_rules! assume {
    ($formula:expr) => {
        ()
    };
}
