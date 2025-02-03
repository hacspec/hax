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
        pub fn new(x: impl Into<u8>) -> Self {
            Int(x.into())
        }
        pub fn get(self) -> u8 {
            self.0
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

    impl Abstraction for i32 {
        type AbstractType = Int;
        fn lift(self) -> Self::AbstractType {
            Int(0)
        }
    }

    impl Concretization<u32> for Int {
        fn concretize(self) -> u32 {
            0
        }
    }
}
