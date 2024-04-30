//! This module provides traits for generic mathematics. This is a
//! smaller and more opinionated version of
//! [num_traits](https://docs.rs/num-traits/latest/num_traits/).
//!
//! This module is designed to make bounded integers ergonomic to use:
//! virtually every operation on bounded integers maps to their
//! underlying type. We also want binary operators to be sufficiently
//! polymophic to allow any combination: for instance, we want the
//! addition of differently bounded u8, or bounded u8 with u8 or vice
//! versa to be possible.
//!
//! Also, the traits in this module are designed to work with types
//! that implement `Copy`.

use core::ops::*;

pub trait Zero: Sized {
    fn zero() -> Self;
}

pub trait One: Sized {
    fn one() -> Self;
}

pub trait NumOps<Rhs = Self, Output = Self>:
    Add<Rhs, Output = Output>
    + Sub<Rhs, Output = Output>
    + Mul<Rhs, Output = Output>
    + Div<Rhs, Output = Output>
    + Rem<Rhs, Output = Output>
{
}

pub trait Bounded {
    fn min_value() -> Self;
    fn max_value() -> Self;
}

pub trait WrappingAdd<Rhs = Self> {
    type Output;
    fn wrapping_add(self, v: Rhs) -> Self::Output;
}

pub trait WrappingSub<Rhs = Self> {
    type Output;
    fn wrapping_sub(self, v: Rhs) -> Self::Output;
}

pub trait WrappingMul<Rhs = Self> {
    type Output;
    fn wrapping_mul(self, v: Rhs) -> Self::Output;
}

pub trait WrappingDiv<Rhs = Self> {
    type Output;
    fn wrapping_div(self, v: Rhs) -> Self::Output;
}

pub trait CheckedAdd<Rhs = Self> {
    type Output;
    fn checked_add(self, v: Rhs) -> Option<Self::Output>;
}

pub trait CheckedSub<Rhs = Self> {
    type Output;
    fn checked_sub(self, v: Rhs) -> Option<Self::Output>;
}

pub trait CheckedMul<Rhs = Self> {
    type Output;
    fn checked_mul(self, v: Rhs) -> Option<Self::Output>;
}

pub trait CheckedDiv<Rhs = Self> {
    type Output;
    fn checked_div(self, v: Rhs) -> Option<Self::Output>;
}

pub trait CheckedNeg {
    type Output;
    fn checked_neg(&self) -> Option<Self::Output>;
}

pub trait FromBytes {
    type BYTES;

    fn from_le_bytes(bytes: Self::BYTES) -> Self;
    fn from_be_bytes(bytes: Self::BYTES) -> Self;
}

pub trait ToBytes: FromBytes {
    fn to_le_bytes(self) -> Self::BYTES;
    fn to_be_bytes(self) -> Self::BYTES;
}

pub trait MachineInt<Output>:
    Copy
    + Bounded
    + PartialOrd
    + Ord
    + PartialEq
    + Eq
    + Zero
    + One
    + Not
    + NumOps<Self, Output>
    + BitAnd<Output = Output>
    + BitOr<Output = Output>
    + BitXor<Output = Output>
    + Shl<Self, Output = Output>
    + Shr<Self, Output = Output>
    + CheckedAdd<Output = Output>
    + CheckedSub<Output = Output>
    + CheckedMul<Output = Output>
    + CheckedDiv<Output = Output>
    + WrappingAdd<Output = Output>
    + WrappingSub<Output = Output>
    + WrappingMul<Output = Output>
    + WrappingDiv<Output = Output>
    + BitOps<Output = Output>
{
}

pub trait BitOps {
    type Output;

    fn count_ones(self) -> u32;
    fn count_zeros(self) -> u32;
    fn leading_ones(self) -> u32;
    fn leading_zeros(self) -> u32;
    fn trailing_ones(self) -> u32;
    fn trailing_zeros(self) -> u32;
    fn rotate_left(self, n: u32) -> Self::Output;
    fn rotate_right(self, n: u32) -> Self::Output;
    fn from_be(x: Self) -> Self::Output;
    fn from_le(x: Self) -> Self::Output;
    fn to_be(self) -> Self::Output;
    fn to_le(self) -> Self::Output;

    fn pow(self, exp: u32) -> Self::Output;
}
