mod abstraction;
pub use abstraction::*;

mod prop;
use prop::*;

use int::*;

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
        ::core::assert!($($arg)*);
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

#[doc(hidden)]
pub fn inline(_: &str) {}

#[doc(hidden)]
pub fn inline_unsafe<T>(_: &str) -> T {
    unreachable!()
}

#[doc(hidden)]
pub fn _internal_loop_invariant<T, P: FnOnce(T) -> bool>(_: P) {}

pub trait Refinement {
    type InnerType;
    fn new(x: Self::InnerType) -> Self;
    fn get(self) -> Self::InnerType;
    fn get_mut(&mut self) -> &mut Self::InnerType;
    fn invariant(value: Self::InnerType) -> bool;
}

pub trait RefineAs<RefinedType> {
    fn into_checked(self) -> RefinedType;
}

pub mod int {
    use core::ops::*;

    #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
    pub struct Int(pub u8);

    impl Int {
        pub fn new(x: impl Into<u128>) -> Self {
            Int(x.into())
        }
    }

    impl Add for Int {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            Int(0)
        }
    }

    impl Sub for Int {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Int(0)
        }
    }

    impl Mul for Int {
        type Output = Self;

        fn mul(self, other: Self) -> Self::Output {
            Int(0)
        }
    }

    impl Div for Int {
        type Output = Self;

        fn div(self, other: Self) -> Self::Output {
            Int(0)
        }
    }

    impl Int {
        pub fn pow2(self) -> Self {
            self
        }
        pub fn _unsafe_from_str(_s: &str) -> Self {
            Int(0)
        }
    }

    pub trait Abstraction {
        type AbstractType;
        fn lift(self) -> Self::AbstractType;
    }

    pub trait Concretization<T> {
        fn concretize(self) -> T;
    }

    impl Abstraction for u8 {
        type AbstractType = Int;
        fn lift(self) -> Self::AbstractType {
            Int(0)
        }
    }
    
    implement_abstraction!(u8 u16 u32 u64 u128 usize);
    implement_abstraction!(i8 i16 i32 i64 i128 isize);
    
    macro_rules! implement_concretize {
        ($ty:ident $method:ident) => {
            impl Concretization<$ty> for Int {
                fn concretize(self) -> $ty {
                    self.0 as $ty
                }
            }
            impl Int {
                pub fn $method(self) -> $ty {
                    self.concretize()
                }
            }
        };
        ($ty:ident $method:ident, $($tt:tt)*) => {
            implement_concretize!($ty $method);
            implement_concretize!($($tt)*);
        };
        () => {};
    }
}
