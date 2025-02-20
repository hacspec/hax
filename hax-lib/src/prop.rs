use crate::abstraction::*;
use core::ops::*;

/// Represent a logical proposition, that may be not computable.
#[derive(Clone, Copy, Debug)]
pub struct Prop(bool);

/// This module provides monomorphic constructors for `Prop`.
/// Hax rewrite more elaborated versions (see `forall` or `AndBit` below) to those monomorphic constructors.
pub mod constructors {
    use super::Prop;
    pub fn from_bool(b: bool) -> Prop {
        Prop(b)
    }
    pub fn and(lhs: Prop, other: Prop) -> Prop {
        Prop(lhs.0 && other.0)
    }
    pub fn or(lhs: Prop, other: Prop) -> Prop {
        Prop(lhs.0 || other.0)
    }
    pub fn not(lhs: Prop) -> Prop {
        Prop(!lhs.0)
    }
    pub fn eq(lhs: Prop, other: Prop) -> Prop {
        Prop(lhs.0 == other.0)
    }
    pub fn ne(lhs: Prop, other: Prop) -> Prop {
        Prop(lhs.0 != other.0)
    }
    pub fn implies(lhs: Prop, other: Prop) -> Prop {
        Prop(lhs.0 || !other.0)
    }
    pub fn forall<A, F: Fn(A) -> Prop>(_pred: F) -> Prop {
        Prop(true)
    }
    pub fn exists<A, F: Fn(A) -> Prop>(_pred: F) -> Prop {
        Prop(true)
    }
}

impl Prop {
    /// Lifts a boolean to a logical proposition.
    pub fn from_bool(b: bool) -> Self {
        constructors::from_bool(b)
    }
    /// Conjuction of two propositions.
    pub fn and(self, other: impl Into<Self>) -> Self {
        constructors::and(self, other.into())
    }
    /// Disjunction of two propositions.
    pub fn or(self, other: impl Into<Self>) -> Self {
        constructors::or(self, other.into())
    }
    /// Negation of a proposition.
    pub fn not(self) -> Self {
        constructors::not(self)
    }
    /// Equality between two propositions.
    pub fn eq(self, other: impl Into<Self>) -> Self {
        constructors::eq(self, other.into())
    }
    /// Equality between two propositions.
    pub fn ne(self, other: impl Into<Self>) -> Self {
        constructors::ne(self, other.into())
    }
    /// Logical implication.
    pub fn implies(self, other: impl Into<Self>) -> Self {
        constructors::implies(self, other.into())
    }
}

impl Abstraction for bool {
    type AbstractType = Prop;
    fn lift(self) -> Self::AbstractType {
        Prop(self)
    }
}

pub trait ToProp {
    fn to_prop(self) -> Prop;
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
pub fn forall<T, U: Into<Prop>>(f: impl Fn(T) -> U) -> Prop {
    constructors::forall(|x| f(x).into())
}

/// The existential quantifier. This should be used only for Hax code: in
/// Rust, this is always true.
///
/// # Example:
///
/// The Rust expression `exists(|x: T| phi(x))` corresponds to `∃ (x: T), phi(x)`.
pub fn exists<T, U: Into<Prop>>(f: impl Fn(T) -> U) -> Prop {
    constructors::exists(|x| f(x).into())
}

/// The logical implication `a ==> b`.
pub fn implies(lhs: impl Into<Prop>, rhs: impl Into<Prop>) -> Prop {
    constructors::implies(lhs.into(), rhs.into())
}
