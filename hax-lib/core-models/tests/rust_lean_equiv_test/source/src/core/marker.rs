//! Equivalence tests for `core::marker::*`. Only the marker types are tested:
//! the marker traits have no methods to observe.

use rust_lean_test_macro::rust_lean_test;

// ----- PhantomData -----------------------------------------------------------

pub struct Tagged<T>(pub u8, pub core::marker::PhantomData<T>);

#[rust_lean_test]
pub fn test_phantom_data_keeps_payload() -> bool {
    let t: Tagged<u32> = Tagged(7, core::marker::PhantomData);
    t.0 == 7
}

#[rust_lean_test]
pub fn test_phantom_data_payload_zero() -> bool {
    let t: Tagged<u32> = Tagged(0, core::marker::PhantomData);
    t.0 == 0
}

#[rust_lean_test]
pub fn test_phantom_data_payload_max() -> bool {
    let t: Tagged<u8> = Tagged(u8::MAX, core::marker::PhantomData);
    t.0 == u8::MAX
}

// ----- PhantomPinned ---------------------------------------------------------

pub struct Pinned(pub u8, pub core::marker::PhantomPinned);

#[rust_lean_test]
pub fn test_phantom_pinned_keeps_payload() -> bool {
    let p = Pinned(7, core::marker::PhantomPinned);
    p.0 == 7
}

#[rust_lean_test]
pub fn test_phantom_pinned_payload_zero() -> bool {
    let p = Pinned(0, core::marker::PhantomPinned);
    p.0 == 0
}

#[rust_lean_test]
pub fn test_phantom_pinned_payload_max() -> bool {
    let p = Pinned(u8::MAX, core::marker::PhantomPinned);
    p.0 == u8::MAX
}

// ----- Variance markers ------------------------------------------------------

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::{
    PhantomContravariant, PhantomContravariantLifetime, PhantomCovariant, PhantomCovariantLifetime,
    PhantomInvariant, PhantomInvariantLifetime,
};

/// Counts the `write` calls it receives.
pub struct Writes(u64);

impl Hasher for Writes {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _bytes: &[u8]) {
        self.0 += 1;
    }
}

#[rust_lean_test]
pub fn test_phantom_covariant_eq() -> bool {
    PhantomCovariant::<u8>::new() == PhantomCovariant::<u8>::default()
}

#[rust_lean_test]
pub fn test_phantom_contravariant_ne() -> bool {
    !(PhantomContravariant::<u8>::new() != PhantomContravariant::<u8>::new())
}

#[rust_lean_test]
pub fn test_phantom_invariant_cmp() -> bool {
    PhantomInvariant::<u8>::new().cmp(&PhantomInvariant::<u8>::default()) == Ordering::Equal
}

#[rust_lean_test]
pub fn test_phantom_covariant_partial_cmp() -> bool {
    PhantomCovariant::<u8>::new().partial_cmp(&PhantomCovariant::<u8>::new())
        == Some(Ordering::Equal)
}

#[rust_lean_test]
pub fn test_phantom_contravariant_hash_writes_nothing() -> bool {
    let mut h = Writes(0);
    PhantomContravariant::<u8>::new().hash(&mut h);
    h.finish() == 0
}

#[rust_lean_test]
pub fn test_phantom_covariant_lifetime_eq() -> bool {
    PhantomCovariantLifetime::new() == PhantomCovariantLifetime::default()
}

#[rust_lean_test]
pub fn test_phantom_contravariant_lifetime_cmp() -> bool {
    PhantomContravariantLifetime::new().cmp(&PhantomContravariantLifetime::new()) == Ordering::Equal
}

#[rust_lean_test]
pub fn test_phantom_invariant_lifetime_hash_writes_nothing() -> bool {
    let mut h = Writes(0);
    PhantomInvariantLifetime::new().hash(&mut h);
    h.finish() == 0
}

#[rust_lean_test]
pub fn test_phantom_invariant_lifetime_clone_eq() -> bool {
    let m = PhantomInvariantLifetime::new();
    m.clone() == m
}
