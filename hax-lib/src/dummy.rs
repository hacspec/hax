mod abstraction;
pub use abstraction::*;

pub mod prop;
pub use prop::*;

pub use int::*;

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
macro_rules! assert_prop {
    ($($arg:tt)*) => {{}};
}

#[macro_export]
macro_rules! assume {
    ($formula:expr) => {
        ()
    };
}

#[doc(hidden)]
pub fn inline(_: &str) {}

#[doc(hidden)]
pub fn inline_unsafe<T>(_: &str) -> T {
    unreachable!()
}

#[doc(hidden)]
pub fn _internal_loop_invariant<T, R: Into<Prop>, P: FnOnce(T) -> R>(_: P) {}

pub trait Refinement {
    type InnerType;
    fn new(x: Self::InnerType) -> Self;
    fn get(self) -> Self::InnerType;
    fn get_mut(&mut self) -> &mut Self::InnerType;
    fn invariant(value: Self::InnerType) -> crate::Prop;
}

pub trait RefineAs<RefinedType> {
    fn into_checked(self) -> RefinedType;
}

pub mod int {
    use core::ops::*;

    macro_rules! int {
        ($lit:expr) => { Int($lit) }
    }

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
            Int(self.0 + other.0)
        }
    }

    impl Sub for Int {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Int(self.0 - other.0)
        }
    }

    impl Mul for Int {
        type Output = Self;

        fn mul(self, other: Self) -> Self::Output {
            Int(self.0 * other.0)
        }
    }

    impl Div for Int {
        type Output = Self;

        fn div(self, other: Self) -> Self::Output {
            Int(self.0 / other.0)
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

    pub trait ToInt {
        fn to_int(self) -> Int;
    }

    pub trait Abstraction {
        type AbstractType;
        fn lift(self) -> Self::AbstractType;
    }

    pub trait Concretization<T> {
        fn concretize(self) -> T;
    }

    macro_rules! implement_abstraction {
        ($ty:ident) => {
            impl Abstraction for $ty {
                type AbstractType = Int;
                fn lift(self) -> Self::AbstractType {
                    Int(0)
                }
            }
            impl ToInt for $ty {
                fn to_int(self) -> Int {
                    self.lift()
                }
            }
        };
        ($($ty:ident)*) => {
            $(implement_abstraction!($ty);)*
        };
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

    implement_concretize!(
        u8    to_u8,
        u16   to_u16,
        u32   to_u32,
        u64   to_u64,
        u128  to_u128,
        usize to_usize,
        i8    to_i8,
        i16   to_i16,
        i32   to_i32,
        i64   to_i64,
        i128  to_i128,
        isize to_isize,
    );
}
