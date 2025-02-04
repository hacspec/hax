use core::ops::*;
use num_traits::cast::ToPrimitive;

mod bigint;
use bigint::*;

#[cfg(feature = "macros")]
pub use hax_lib_macros::int;

/// Mathematical integers for writting specifications. Mathematical
/// integers are unbounded and arithmetic operation on them never over
/// or underflow.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Int(BigInt);

impl Int {
    fn new(x: impl Into<num_bigint::BigInt>) -> Self {
        Int(BigInt::new(&x.into()))
    }
    fn get(self) -> num_bigint::BigInt {
        self.0.get()
    }
}

impl Add for Int {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::new(self.get() + other.get())
    }
}

impl Sub for Int {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self::new(self.get() - other.get())
    }
}

impl Mul for Int {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        Self::new(self.get() * other.get())
    }
}

impl Div for Int {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        Self::new(self.get() / other.get())
    }
}

impl Rem for Int {
    type Output = Self;

    fn rem(self, other: Self) -> Self::Output {
        Self::new(self.get() % other.get())
    }
}

impl Int {
    /// Raises `2` at the power `self`
    pub fn pow2(self) -> Self {
        let exponent = self.get().to_u32().expect("Exponent doesn't fit in a u32");
        Self::new(num_bigint::BigInt::from(2u8).pow(exponent))
    }

    /// Constructs a `Int` out of a string literal. This function
    /// assumes its argument consists only of decimal digits, with
    /// optionally a minus sign prefix.
    pub fn _unsafe_from_str(s: &str) -> Self {
        use core::str::FromStr;
        Self::new(num_bigint::BigInt::from_str(s).unwrap())
    }
}

/// Marks a type as abstractable: its values can be mapped to an
/// idealized version of the type. For instance, machine integers,
/// which have bounds, can be mapped to mathematical integers.
///
/// Each type can have only one abstraction.
pub trait Abstraction {
    /// What is the ideal type values should be mapped to?
    type AbstractType;
    /// Maps a concrete value to its abstract counterpart
    fn lift(self) -> Self::AbstractType;
}

/// Marks a type as abstract: its values can be lowered to concrete
/// values. This might panic.
pub trait Concretization<T> {
    /// Maps an abstract value and lowers it to its concrete counterpart.
    fn concretize(self) -> T;
}

/// Instead of defining one overloaded instance, which relies
/// explicitely on `num_bigint`:
///
/// ```ignore
/// impl<T: Into<num_bigint::BigInt>> Abstraction for T {
///     type AbstractType = Int;
///     fn lift(self) -> Self::AbstractType {
///         Int::new(self.into())
///     }
/// }
/// ```
///
/// We define an instance per machine type: we don't want the
/// interface of this module to rely specifically on
/// `num_bigint`. This module should be a very thin layer.
macro_rules! implement_abstraction {
    ($ty:ident) => {
        impl Abstraction for $ty {
            type AbstractType = Int;
            fn lift(self) -> Self::AbstractType {
                Int::new(num_bigint::BigInt::from(self))
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
                let concretized = self.get().$method();
                debug_assert!(concretized.is_some());
                concretized.unwrap().into()
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
