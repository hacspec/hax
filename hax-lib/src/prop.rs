use crate::abstraction::*;
use core::ops::*;

pub struct Prop(bool);

pub trait ToProp {
    fn to_prop(self) -> Prop;
}

impl Abstraction for bool {
    type AbstractType = Prop;
    fn lift(self) -> Self::AbstractType {
        Prop(self)
    }
}

impl ToProp for bool {
    fn to_prop(self) -> Prop {
        self.lift()
    }
}

impl From<bool> for Prop {
    fn from(value: bool) -> Self {
        Prop(value)
    }
}

impl<T: Into<Prop>> BitAnd<T> for Prop {
    type Output = Prop;
    fn bitand(self, rhs: T) -> Self::Output {
        Prop(self.0 & rhs.into().0)
    }
}

impl<T: Into<Prop>> BitOr<T> for Prop {
    type Output = Prop;
    fn bitor(self, rhs: T) -> Self::Output {
        Prop(self.0 | rhs.into().0)
    }
}

impl Not for Prop {
    type Output = Prop;
    fn not(self) -> Self::Output {
        Prop(!self.0)
    }
}

/// The universal quantifier. This should be used only for Hax code: in
/// Rust, this is always true.
///
/// # Example:
///
/// The Rust expression `forall(|x: T| phi(x))` corresponds to `∀ (x: T), phi(x)`.
pub fn forall<T,U:Into<Prop>>(_f: impl Fn(T) -> U) -> Prop {
    Prop(true)
}

/// The existential quantifier. This should be used only for Hax code: in
/// Rust, this is always true.
///
/// # Example:
///
/// The Rust expression `exists(|x: T| phi(x))` corresponds to `∃ (x: T), phi(x)`.
pub fn exists<T,U:Into<Prop>>(_f: impl Fn(T) -> U) -> Prop {
    Prop(true)
}

/// The logical implication `a ==> b`.
pub fn implies<T:Into<Prop>, U:Into<Prop>>(lhs: T, rhs: impl Fn() -> U) -> Prop {
    !lhs.into() | rhs().into()
}