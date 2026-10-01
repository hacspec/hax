//! Equivalence tests for `core::option::Option::*`.

use crate::helpers::none_u8;
use crate::helpers::{Bumped, CopyBumped, Keyed, keyed};
use rust_lean_test_macro::rust_lean_test;

// ----- is_some / is_none -----------------------------------------------------

#[rust_lean_test]
pub fn test_is_some_none_u8() -> bool {
    none_u8().is_some() == false
}

#[rust_lean_test]
pub fn test_is_some_some_zero() -> bool {
    Some(0u8).is_some() == true
}

#[rust_lean_test]
pub fn test_is_some_some_max() -> bool {
    Some(u8::MAX).is_some() == true
}

#[rust_lean_test]
pub fn test_is_none_none_u8() -> bool {
    none_u8().is_none() == true
}

#[rust_lean_test]
pub fn test_is_none_some_zero() -> bool {
    Some(0u8).is_none() == false
}

#[rust_lean_test]
pub fn test_is_none_some_max() -> bool {
    Some(u8::MAX).is_none() == false
}

// ----- is_some_and -----------------------------------------------------------

#[rust_lean_test]
pub fn test_is_some_and_some_true() -> bool {
    Some(4u8).is_some_and(|x| x > 0) == true
}

#[rust_lean_test]
pub fn test_is_some_and_some_false() -> bool {
    Some(0u8).is_some_and(|x| x > 0) == false
}

#[rust_lean_test]
pub fn test_is_some_and_none() -> bool {
    none_u8().is_some_and(|x| x > 0) == false
}

// ----- is_none_or ------------------------------------------------------------

#[rust_lean_test]
pub fn test_is_none_or_some_true() -> bool {
    Some(4u8).is_none_or(|x| x > 0) == true
}

#[rust_lean_test]
pub fn test_is_none_or_some_false() -> bool {
    Some(0u8).is_none_or(|x| x > 0) == false
}

#[rust_lean_test]
pub fn test_is_none_or_none() -> bool {
    none_u8().is_none_or(|x| x > 0) == true
}

// ----- as_ref ----------------------------------------------------------------

// TODO(as_ref): as_ref returns Option<&T> which involves references-to-references
// through extraction; skip until references are exercised.

// ----- expect ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_expect_some_zero() -> bool {
    Some(0u8).expect("msg") == 0
}

#[rust_lean_test]
pub fn test_expect_some_max() -> bool {
    Some(u8::MAX).expect("msg") == u8::MAX
}

#[rust_lean_test]
pub fn test_expect_some_mid() -> bool {
    Some(42u8).expect("msg") == 42
}

// ----- unwrap ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_some_zero() -> bool {
    Some(0u8).unwrap() == 0
}

#[rust_lean_test]
pub fn test_unwrap_some_max() -> bool {
    Some(u8::MAX).unwrap() == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_some_mid() -> bool {
    Some(7u8).unwrap() == 7
}

// ----- unwrap_or -------------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_some_zero() -> bool {
    Some(0u8).unwrap_or(42) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_some_max() -> bool {
    Some(u8::MAX).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_none_default_zero() -> bool {
    none_u8().unwrap_or(0) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_none_default_max() -> bool {
    none_u8().unwrap_or(u8::MAX) == u8::MAX
}

// ----- unwrap_or_else --------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_else_some_zero() -> bool {
    Some(0u8).unwrap_or_else(|| 42) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_else_some_max() -> bool {
    Some(u8::MAX).unwrap_or_else(|| 0) == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_else_none() -> bool {
    none_u8().unwrap_or_else(|| 7) == 7
}

// ----- unwrap_or_default -----------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_default_some_zero() -> bool {
    Some(0u8).unwrap_or_default() == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_default_some_max() -> bool {
    Some(u8::MAX).unwrap_or_default() == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_default_none() -> bool {
    none_u8().unwrap_or_default() == 0
}

// ----- map -------------------------------------------------------------------

// TODO(closure-extraction-map): `Option::map` returns `Option<U>`; observing the
// result requires either `Option::PartialEq` (blocked by option-eq-extraction)
// or destructuring through `match`, but the latter goes back through
// `Option::PartialEq` once we compare the inner value. Revisit alongside
// option-eq-extraction.

#[rust_lean_test]
pub fn test_map_some_via_unwrap_or() -> bool {
    Some(3u8).map(|x| x + 1).unwrap_or(0) == 4
}

#[rust_lean_test]
pub fn test_map_none_via_unwrap_or() -> bool {
    none_u8().map(|x| x + 1).unwrap_or(99) == 99
}

#[rust_lean_test]
pub fn test_map_some_is_some() -> bool {
    Some(3u8).map(|x| x + 1).is_some()
}

#[rust_lean_test]
pub fn test_map_none_is_none() -> bool {
    none_u8().map(|x| x + 1).is_none()
}

// ----- map_or ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_map_or_some_zero() -> bool {
    Some(3u8).map_or(0u8, |x| x + 1) == 4
}

#[rust_lean_test]
pub fn test_map_or_some_max() -> bool {
    Some(0u8).map_or(99u8, |x| x + 1) == 1
}

#[rust_lean_test]
pub fn test_map_or_none() -> bool {
    none_u8().map_or(99u8, |x| x + 1) == 99
}

// ----- map_or_else -----------------------------------------------------------

// TODO(closure-extraction-order): `Option::map_or_else` takes (default: D, f: F)
// in source order but the model lists the trait instances in (F, D) order, so
// Aeneas emits them swapped and the Lean elaboration fails for the `None`
// branch. Revisit once the closure-instance ordering is fixed.

// ----- map_or_default --------------------------------------------------------

// TODO(map_or_default-unstable): `Option::map_or_default` is gated behind
// `result_option_map_or_default` on stable. Revisit once it stabilises.

// ----- ok_or -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_ok_or_some_zero() -> bool {
    matches!(Some(0u8).ok_or(99u8), Ok(0))
}

#[rust_lean_test]
pub fn test_ok_or_some_max() -> bool {
    matches!(Some(u8::MAX).ok_or(0u8), Ok(v) if v == u8::MAX)
}

#[rust_lean_test]
pub fn test_ok_or_none_err_zero() -> bool {
    matches!(none_u8().ok_or(0u8), Err(0))
}

#[rust_lean_test]
pub fn test_ok_or_none_err_max() -> bool {
    matches!(none_u8().ok_or(u8::MAX), Err(v) if v == u8::MAX)
}

// ----- ok_or_else ------------------------------------------------------------

#[rust_lean_test]
pub fn test_ok_or_else_some() -> bool {
    matches!(Some(7u8).ok_or_else(|| 99u8), Ok(7))
}

#[rust_lean_test]
pub fn test_ok_or_else_none() -> bool {
    matches!(none_u8().ok_or_else(|| 42u8), Err(42))
}

// ----- and_then --------------------------------------------------------------

#[rust_lean_test]
pub fn test_and_then_some_to_some() -> bool {
    Some(3u8).and_then(|x| Some(x + 1)).unwrap_or(0) == 4
}

#[rust_lean_test]
pub fn test_and_then_some_to_none() -> bool {
    Some(3u8).and_then(|_| none_u8()).is_none()
}

#[rust_lean_test]
pub fn test_and_then_none() -> bool {
    none_u8().and_then(|x| Some(x + 1)).is_none()
}

// ----- filter ----------------------------------------------------------------

// TODO(closure-by-ref-extraction): `Option::filter` takes `FnOnce(&T) -> bool`;
// Aeneas trips on the borrow with "Region ids should not be visited directly".
// Revisit once closures whose parameter is a reference extract.

// ----- or --------------------------------------------------------------------

#[rust_lean_test]
pub fn test_or_some_some() -> bool {
    Some(0u8).or(Some(99u8)).unwrap_or(7) == 0
}

#[rust_lean_test]
pub fn test_or_some_none() -> bool {
    Some(u8::MAX).or(none_u8()).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_or_none_some() -> bool {
    none_u8().or(Some(42u8)).unwrap_or(0) == 42
}

#[rust_lean_test]
pub fn test_or_none_none() -> bool {
    none_u8().or(none_u8()).is_none()
}

// ----- or_else ---------------------------------------------------------------

#[rust_lean_test]
pub fn test_or_else_some_kept() -> bool {
    Some(0u8).or_else(|| Some(99u8)).unwrap_or(7) == 0
}

#[rust_lean_test]
pub fn test_or_else_some_max_kept() -> bool {
    Some(u8::MAX).or_else(|| none_u8()).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_or_else_none_to_some() -> bool {
    none_u8().or_else(|| Some(42u8)).unwrap_or(0) == 42
}

#[rust_lean_test]
pub fn test_or_else_none_to_none() -> bool {
    none_u8().or_else(|| none_u8()).is_none()
}

// ----- xor -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_xor_some_none() -> bool {
    Some(7u8).xor(none_u8()).unwrap_or(0) == 7
}

#[rust_lean_test]
pub fn test_xor_none_some() -> bool {
    none_u8().xor(Some(u8::MAX)).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_xor_some_some() -> bool {
    Some(0u8).xor(Some(99u8)).is_none()
}

#[rust_lean_test]
pub fn test_xor_none_none() -> bool {
    none_u8().xor(none_u8()).is_none()
}

// ----- zip -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_zip_some_some_zero() -> bool {
    match Some(0u8).zip(Some(0u8)) {
        Some((a, b)) => a == 0 && b == 0,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_zip_some_some_max() -> bool {
    match Some(u8::MAX).zip(Some(0u8)) {
        Some((a, b)) => a == u8::MAX && b == 0,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_zip_some_none() -> bool {
    Some(7u8).zip(none_u8()).is_none()
}

#[rust_lean_test]
pub fn test_zip_none_some() -> bool {
    none_u8().zip(Some(7u8)).is_none()
}

#[rust_lean_test]
pub fn test_zip_none_none() -> bool {
    none_u8().zip(none_u8()).is_none()
}

// ----- inspect ---------------------------------------------------------------

// TODO(closure-by-ref-extraction): `Option::inspect` takes `FnOnce(&T)`;
// Aeneas trips on the borrow with "Region ids should not be visited directly".
// Revisit once closures whose parameter is a reference extract.

// ----- flatten ---------------------------------------------------------------

#[rust_lean_test]
pub fn test_flatten_some_some_zero() -> bool {
    Some(Some(0u8)).flatten().unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_flatten_some_some_max() -> bool {
    Some(Some(u8::MAX)).flatten().unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_flatten_some_none() -> bool {
    Some(none_u8()).flatten().is_none()
}

// ----- Default ---------------------------------------------------------------

// TODO(default-trait): testing Default for Option<T> via the model trait requires
// importing the model's Default trait; revisit alongside Default coverage.

// ----------------------------------------------------------------------------
// `take` carries `#[cfg_attr(hax_backend_lean, hax_lib::exclude)]`, so Aeneas
// does not extract its body and the Lean side resolves to a hand-written
// definition in `lean/CoreModels/Core/FunsPrologue.lean`. The sections below
// widen the element types the other three methods are exercised at.
// ----------------------------------------------------------------------------

use crate::helpers::{none_i32, none_u32};

// ----- is_some (further element types) --------------------------------------

#[rust_lean_test]
pub fn test_is_some_some_u8_zero() -> bool {
    Some(0u8).is_some() == true
}

#[rust_lean_test]
pub fn test_is_some_some_u8_max() -> bool {
    Some(u8::MAX).is_some() == true
}

#[rust_lean_test]
pub fn test_is_some_some_u32() -> bool {
    Some(123u32).is_some() == true
}

#[rust_lean_test]
pub fn test_is_some_none_u32() -> bool {
    none_u32().is_some() == false
}

#[rust_lean_test]
pub fn test_is_some_some_bool() -> bool {
    Some(true).is_some() == true
}

#[rust_lean_test]
pub fn test_is_some_none_bool() -> bool {
    crate::helpers::none_bool().is_some() == false
}

// ----- is_none (further element types) --------------------------------------

#[rust_lean_test]
pub fn test_is_none_some_u8_zero() -> bool {
    Some(0u8).is_none() == false
}

#[rust_lean_test]
pub fn test_is_none_some_u8_max() -> bool {
    Some(u8::MAX).is_none() == false
}

#[rust_lean_test]
pub fn test_is_none_some_i32() -> bool {
    Some(-1i32).is_none() == false
}

#[rust_lean_test]
pub fn test_is_none_none_i32() -> bool {
    none_i32().is_none() == true
}

#[rust_lean_test]
pub fn test_is_none_some_bool() -> bool {
    Some(false).is_none() == false
}

#[rust_lean_test]
pub fn test_is_none_none_bool() -> bool {
    crate::helpers::none_bool().is_none() == true
}

// ----- unwrap_or (further element types) ------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_some_u8_zero() -> bool {
    Some(0u8).unwrap_or(42) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_some_u8_max() -> bool {
    Some(u8::MAX).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_none_u8_small_default() -> bool {
    none_u8().unwrap_or(7) == 7
}

#[rust_lean_test]
pub fn test_unwrap_or_none_u8_max_default() -> bool {
    none_u8().unwrap_or(u8::MAX) == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_some_u32_small() -> bool {
    Some(5u32).unwrap_or(99) == 5
}

#[rust_lean_test]
pub fn test_unwrap_or_none_u32_max_default() -> bool {
    none_u32().unwrap_or(u32::MAX) == u32::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_some_bool() -> bool {
    Some(true).unwrap_or(false) == true
}

#[rust_lean_test]
pub fn test_unwrap_or_none_bool() -> bool {
    crate::helpers::none_bool().unwrap_or(true) == true
}

// ----- take (manually defined in Lean, not extracted) -----------------------

#[rust_lean_test]
pub fn test_manual_take_some_u8_returns_old() -> bool {
    let mut x: Option<u8> = Some(9);
    let old = x.take();
    old == Some(9)
}

#[rust_lean_test]
pub fn test_manual_take_some_u8_replaces_with_none() -> bool {
    let mut x: Option<u8> = Some(9);
    let _ = x.take();
    x.is_some() == false
}

#[rust_lean_test]
pub fn test_manual_take_some_u8_max_returns_old() -> bool {
    let mut x: Option<u8> = Some(u8::MAX);
    let old = x.take();
    old == Some(u8::MAX) && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_none_u8_returns_none() -> bool {
    let mut x: Option<u8> = none_u8();
    let old = x.take();
    old.is_none() && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_some_u32() -> bool {
    let mut x: Option<u32> = Some(123);
    let old = x.take();
    old == Some(123) && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_none_u32() -> bool {
    let mut x: Option<u32> = none_u32();
    let old = x.take();
    old.is_none() && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_some_bool() -> bool {
    let mut x: Option<bool> = Some(true);
    let old = x.take();
    old == Some(true) && x.is_none()
}

// ----- PartialEq: `Option<T> == Option<T>` -----------------------------------

#[rust_lean_test]
pub fn test_option_eq_some_same() -> bool {
    (Some(5u8) == Some(5u8)) == true
}

#[rust_lean_test]
pub fn test_option_eq_some_diff() -> bool {
    (Some(5u8) == Some(6u8)) == false
}

#[rust_lean_test]
pub fn test_option_eq_none_none() -> bool {
    (none_u8() == none_u8()) == true
}

#[rust_lean_test]
pub fn test_option_eq_some_none() -> bool {
    (Some(5u8) == none_u8()) == false
}

#[rust_lean_test]
pub fn test_option_eq_none_some() -> bool {
    (none_u8() == Some(5u8)) == false
}

// ----- dictionary-applying tests ---------------------------------------------

#[rust_lean_test]
pub fn test_clone_some_applies_element_clone() -> bool {
    let x = Some(Bumped(1));
    match x.clone() {
        Some(b) => b.0 == 2,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_clone_none_of_a_cloneable_element() -> bool {
    let x: Option<Bumped> = None;
    x.clone().is_none()
}

#[rust_lean_test]
pub fn test_eq_some_goes_through_the_dictionary() -> bool {
    Some(keyed(5, 1)) == Some(keyed(5, 2))
}

#[rust_lean_test]
pub fn test_ne_some_goes_through_the_dictionary() -> bool {
    (Some(keyed(5, 1)) != Some(keyed(5, 2))) == false
}

#[rust_lean_test]
pub fn test_eq_some_differing_keys() -> bool {
    (Some(keyed(5, 1)) == Some(keyed(6, 1))) == false
}

// The mismatch arm never reaches the element dictionary.
#[rust_lean_test]
pub fn test_eq_some_vs_none() -> bool {
    let n: Option<Keyed> = None;
    (Some(keyed(5, 1)) == n) == false
}

// ----- and -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_and_some_some() -> bool {
    Some(0u8).and(Some(7u8)).unwrap_or(99) == 7
}

#[rust_lean_test]
pub fn test_and_some_some_max() -> bool {
    Some(u8::MAX).and(Some(0u8)).unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_and_some_none() -> bool {
    Some(0u8).and(none_u8()).is_none()
}

#[rust_lean_test]
pub fn test_and_none_some() -> bool {
    none_u8().and(Some(7u8)).is_none()
}

#[rust_lean_test]
pub fn test_and_none_none() -> bool {
    none_u8().and(none_u8()).is_none()
}

// ----- unwrap_unchecked ------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_unchecked_some_zero() -> bool {
    unsafe { Some(0u8).unwrap_unchecked() == 0 }
}

#[rust_lean_test]
pub fn test_unwrap_unchecked_some_max() -> bool {
    unsafe { Some(u8::MAX).unwrap_unchecked() == u8::MAX }
}

#[rust_lean_test]
pub fn test_unwrap_unchecked_some_mid() -> bool {
    unsafe { Some(7u8).unwrap_unchecked() == 7 }
}

// ----- unzip -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_unzip_some_zero() -> bool {
    let (a, b) = Some((0u8, 0u8)).unzip();
    a.unwrap_or(99) == 0 && b.unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_unzip_some_edges() -> bool {
    let (a, b) = Some((u8::MAX, 0u8)).unzip();
    a.unwrap_or(0) == u8::MAX && b.unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_unzip_none() -> bool {
    let (a, b) = crate::helpers::none_pair_u8().unzip();
    a.is_none() && b.is_none()
}

// ----- transpose -------------------------------------------------------------

// Typed via the return type: Aeneas cannot print unpinned `Result` params.
fn some_ok_u8(v: u8) -> Option<Result<u8, u8>> {
    Some(Ok(v))
}
fn some_err_u8(e: u8) -> Option<Result<u8, u8>> {
    Some(Err(e))
}
fn none_result_u8() -> Option<Result<u8, u8>> {
    let mut x: Option<Result<u8, u8>> = Some(Ok(0));
    x.take();
    x
}

#[rust_lean_test]
pub fn test_transpose_some_ok_zero() -> bool {
    match some_ok_u8(0).transpose() {
        Ok(o) => o.unwrap_or(99) == 0,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_transpose_some_ok_max() -> bool {
    match some_ok_u8(u8::MAX).transpose() {
        Ok(o) => o.unwrap_or(0) == u8::MAX,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_transpose_some_err() -> bool {
    match some_err_u8(3).transpose() {
        Ok(_) => false,
        Err(e) => e == 3,
    }
}

#[rust_lean_test]
pub fn test_transpose_none() -> bool {
    match none_result_u8().transpose() {
        Ok(o) => o.is_none(),
        Err(_) => false,
    }
}

// ----- reduce ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_reduce_some_some() -> bool {
    Some(1u8).reduce(Some(2u8), |a, b| a + b) == Some(3)
}

#[rust_lean_test]
pub fn test_reduce_some_none() -> bool {
    Some(1u8).reduce(none_u8(), |a, b| a + b) == Some(1)
}

#[rust_lean_test]
pub fn test_reduce_none_none() -> bool {
    none_u8().reduce(none_u8(), |a, b| a + b).is_none()
}

// ----- iter / into_iter ------------------------------------------------------

#[rust_lean_test]
pub fn test_iter_some_yields_the_value() -> bool {
    let o: Option<u8> = Some(7);
    let mut it = o.iter();
    it.next() == Some(&7) && it.next().is_none()
}

#[rust_lean_test]
pub fn test_iter_none_is_empty() -> bool {
    none_u8().iter().next().is_none()
}

#[rust_lean_test]
pub fn test_into_iter_some() -> bool {
    let mut it = Some(u8::MAX).into_iter();
    it.next() == Some(u8::MAX) && it.next().is_none()
}

#[rust_lean_test]
pub fn test_into_iter_none() -> bool {
    none_u8().into_iter().next().is_none()
}

// ----- as_slice --------------------------------------------------------------

#[rust_lean_test]
pub fn test_as_slice_some_len() -> bool {
    let o: Option<u8> = Some(7);
    let s = o.as_slice();
    s.len() == 1 && s[0] == 7
}

#[rust_lean_test]
pub fn test_as_slice_none_len() -> bool {
    none_u8().as_slice().len() == 0
}

// ----- as_mut / as_deref / as_deref_mut --------------------------------------

#[rust_lean_test]
pub fn test_as_mut_some_mutates() -> bool {
    let mut o: Option<u8> = Some(0);
    if let Some(v) = o.as_mut() {
        *v = u8::MAX;
    }
    o == Some(u8::MAX)
}

#[rust_lean_test]
pub fn test_as_mut_none() -> bool {
    let mut o = none_u8();
    o.as_mut().is_none()
}

#[rust_lean_test]
pub fn test_as_deref_some() -> bool {
    let v: u8 = 7;
    let o: Option<&u8> = Some(&v);
    o.as_deref() == Some(&7)
}

#[rust_lean_test]
pub fn test_as_deref_none() -> bool {
    let n = none_u8();
    let o: Option<&u8> = n.as_ref();
    o.as_deref().is_none()
}

// Rust-only: `as_mut_slice` has no Lean definition (opaque in the model).
#[cfg(test)]
mod as_mut_slice {
    #[test]
    fn test_as_mut_slice_some() {
        let mut o: Option<u8> = Some(0);
        o.as_mut_slice()[0] = u8::MAX;
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_as_mut_slice_none() {
        let mut o: Option<u8> = None;
        assert!(o.as_mut_slice().is_empty());
    }
}

// Rust-only: the model has no `DerefMut for &mut T` in Lean, whose reborrow aeneas
// mistranslates.
#[cfg(test)]
mod as_deref_mut {
    #[test]
    fn test_as_deref_mut_some_mutates_through() {
        let mut v: u8 = 0;
        let mut o: Option<&mut u8> = Some(&mut v);
        if let Some(inner) = o.as_deref_mut() {
            *inner = u8::MAX;
        }
        assert!(v == u8::MAX);
    }
}

// ----- cloned / copied -------------------------------------------------------

#[rust_lean_test]
pub fn test_cloned_some() -> bool {
    let v: u8 = 7;
    let o: Option<&u8> = Some(&v);
    o.cloned() == Some(7u8)
}

#[rust_lean_test]
pub fn test_copied_some() -> bool {
    let v: u8 = u8::MAX;
    Some(&v).copied() == Some(u8::MAX)
}

#[rust_lean_test]
pub fn test_copied_some_does_not_clone() -> bool {
    let v = CopyBumped(0);
    let x: Option<&CopyBumped> = Some(&v);
    match x.copied() {
        Some(c) => c.0 == 0,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_copied_none() -> bool {
    None::<&u8>.copied() == None
}
