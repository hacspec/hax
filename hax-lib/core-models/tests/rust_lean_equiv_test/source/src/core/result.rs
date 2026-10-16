//! Equivalence tests for `core::result::Result::*`.

use crate::helpers::{Bumped, CopyBumped, Keyed, keyed};
use rust_lean_test_macro::rust_lean_test;

// Local helpers: function-level return-type annotations survive Aeneas
// extraction even when the variant only pins one of the two type params.
// Without these, `Ok(0u8)` leaves `E` unknown and `Err(0u8)` leaves `T`
// unknown, producing Lean output that fails to elaborate.
fn ok_u8_u8(v: u8) -> Result<u8, u8> {
    Ok(v)
}
fn err_u8_u8(e: u8) -> Result<u8, u8> {
    Err(e)
}

// ----- is_ok / is_err --------------------------------------------------------

#[rust_lean_test]
pub fn test_is_ok_ok_zero() -> bool {
    ok_u8_u8(0).is_ok() == true
}

#[rust_lean_test]
pub fn test_is_ok_ok_max() -> bool {
    ok_u8_u8(u8::MAX).is_ok() == true
}

#[rust_lean_test]
pub fn test_is_ok_err_zero() -> bool {
    err_u8_u8(0).is_ok() == false
}

#[rust_lean_test]
pub fn test_is_ok_err_max() -> bool {
    err_u8_u8(u8::MAX).is_ok() == false
}

#[rust_lean_test]
pub fn test_is_err_ok_zero() -> bool {
    ok_u8_u8(0).is_err() == false
}

#[rust_lean_test]
pub fn test_is_err_err_zero() -> bool {
    err_u8_u8(0).is_err() == true
}

#[rust_lean_test]
pub fn test_is_err_err_max() -> bool {
    err_u8_u8(u8::MAX).is_err() == true
}

// ----- is_ok_and -------------------------------------------------------------

// ----- is_err_and ------------------------------------------------------------

// ----- as_ref ----------------------------------------------------------------

// TODO(as_ref): as_ref returns Result<&T, &E> which involves references-to-references
// through extraction; skip until references are exercised.

// ----- expect ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_expect_ok_zero() -> bool {
    ok_u8_u8(0).expect("msg") == 0
}

#[rust_lean_test]
pub fn test_expect_ok_max() -> bool {
    ok_u8_u8(u8::MAX).expect("msg") == u8::MAX
}

#[rust_lean_test]
pub fn test_expect_ok_mid() -> bool {
    ok_u8_u8(42).expect("msg") == 42
}

// ----- unwrap ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_ok_zero() -> bool {
    ok_u8_u8(0).unwrap() == 0
}

#[rust_lean_test]
pub fn test_unwrap_ok_max() -> bool {
    ok_u8_u8(u8::MAX).unwrap() == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_ok_mid() -> bool {
    ok_u8_u8(7).unwrap() == 7
}

// ----- unwrap_err ------------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_err_err_zero() -> bool {
    err_u8_u8(0).unwrap_err() == 0
}

#[rust_lean_test]
pub fn test_unwrap_err_err_max() -> bool {
    err_u8_u8(u8::MAX).unwrap_err() == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_err_err_mid() -> bool {
    err_u8_u8(7).unwrap_err() == 7
}

// ----- unwrap_or -------------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_ok_zero() -> bool {
    ok_u8_u8(0).unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_ok_max() -> bool {
    ok_u8_u8(u8::MAX).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_err_default_zero() -> bool {
    err_u8_u8(99).unwrap_or(0) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_err_default_max() -> bool {
    err_u8_u8(0).unwrap_or(u8::MAX) == u8::MAX
}

// ----- unwrap_or_else --------------------------------------------------------

// ----- unwrap_or_default -----------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_default_ok_zero() -> bool {
    ok_u8_u8(0).unwrap_or_default() == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_default_ok_max() -> bool {
    ok_u8_u8(u8::MAX).unwrap_or_default() == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_default_err() -> bool {
    err_u8_u8(u8::MAX).unwrap_or_default() == 0
}

// ----- map -------------------------------------------------------------------

// ----- map_or ----------------------------------------------------------------

// ----- map_or_else -----------------------------------------------------------

// ----- map_or_default --------------------------------------------------------

// TODO(result-method-missing: `Result::map_or_default` missing from extracted
// Lean (see map).)

// ----- map_err ---------------------------------------------------------------
// `Result::map_err` is now modeled and extracted, but can't be exercised here:
// the model takes CoreModels' `FnOnce` while the equiv call site supplies
// Aeneas's `BuiltinFnOnce`, and the two don't unify.
// TODO(closure-extraction): re-enable once core-models closures extract as
// `core.ops.function.FnOnce` in the equiv pipeline.

// ----- inspect / inspect_err -------------------------------------------------

// ----- ok --------------------------------------------------------------------

#[rust_lean_test]
pub fn test_ok_ok_zero() -> bool {
    ok_u8_u8(0).ok().unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_ok_ok_max() -> bool {
    ok_u8_u8(u8::MAX).ok().unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_ok_err() -> bool {
    err_u8_u8(7).ok().is_none()
}

// ----- err -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_err_err_zero() -> bool {
    err_u8_u8(0).err().unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_err_err_max() -> bool {
    err_u8_u8(u8::MAX).err().unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_err_ok() -> bool {
    ok_u8_u8(7).err().is_none()
}

// ----- and -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_and_ok_ok() -> bool {
    ok_u8_u8(0).and(ok_u8_u8(7)).unwrap_or(99) == 7
}

#[rust_lean_test]
pub fn test_and_ok_err() -> bool {
    ok_u8_u8(0).and(err_u8_u8(42)).unwrap_err() == 42
}

#[rust_lean_test]
pub fn test_and_err_ok() -> bool {
    err_u8_u8(99).and(ok_u8_u8(0)).unwrap_err() == 99
}

#[rust_lean_test]
pub fn test_and_err_err() -> bool {
    err_u8_u8(u8::MAX).and(err_u8_u8(0)).unwrap_err() == u8::MAX
}

// ----- and_then --------------------------------------------------------------

// ----- or --------------------------------------------------------------------

#[rust_lean_test]
pub fn test_or_ok_ok() -> bool {
    ok_u8_u8(0).or(ok_u8_u8(99)).unwrap_or(7) == 0
}

#[rust_lean_test]
pub fn test_or_ok_err() -> bool {
    ok_u8_u8(u8::MAX).or(err_u8_u8(42)).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_or_err_ok() -> bool {
    err_u8_u8(99).or(ok_u8_u8(42)).unwrap_or(0) == 42
}

#[rust_lean_test]
pub fn test_or_err_err() -> bool {
    err_u8_u8(99).or(err_u8_u8(7)).unwrap_err() == 7
}

// ----- or_else ---------------------------------------------------------------

// ----- cloned ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_cloned_ok() -> bool {
    let v: u8 = 7;
    let r: Result<&u8, u8> = Ok(&v);
    r.cloned() == Ok(7u8)
}

#[rust_lean_test]
pub fn test_cloned_err() -> bool {
    let r: Result<&u8, u8> = Err(u8::MAX);
    r.cloned() == Err(u8::MAX)
}

fn ok_bumped_ref(b: &Bumped) -> Result<&Bumped, u8> {
    Ok(b)
}

#[rust_lean_test]
pub fn test_cloned_applies_clone() -> bool {
    let b = Bumped(0);
    match ok_bumped_ref(&b).cloned() {
        Ok(c) => c.0 == 1,
        Err(_) => false,
    }
}

// ----- transpose -------------------------------------------------------------

// Helpers for Result<Option<u8>, u8>: typed via function return type.
fn ok_some_u8(v: u8) -> Result<Option<u8>, u8> {
    Ok(Some(v))
}
fn ok_none_u8() -> Result<Option<u8>, u8> {
    let mut x: Option<u8> = Some(0);
    x.take();
    Ok(x)
}
fn err_outer_u8(e: u8) -> Result<Option<u8>, u8> {
    Err(e)
}

#[rust_lean_test]
pub fn test_transpose_ok_some_zero() -> bool {
    match ok_some_u8(0).transpose() {
        Some(Ok(v)) => v == 0,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_transpose_ok_some_max() -> bool {
    match ok_some_u8(u8::MAX).transpose() {
        Some(Ok(v)) => v == u8::MAX,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_transpose_ok_none() -> bool {
    ok_none_u8().transpose().is_none()
}

#[rust_lean_test]
pub fn test_transpose_err() -> bool {
    match err_outer_u8(7).transpose() {
        Some(Err(e)) => e == 7,
        _ => false,
    }
}

// ----- flatten ---------------------------------------------------------------

// TODO(result-flatten-unstable): `Result::flatten` is gated behind the
// `result_flattening` feature on stable std. The model defines `flatten`
// directly so the Lean side works, but the Rust side cannot call
// `r.flatten()` on stable. Revisit once `result_flattening` stabilises.

// ----- `?` operator (Try::branch + FromResidual::from_residual) --------------
// `?` is stable even though `Try`/`FromResidual` aren't, so it's the only way to
// drive the whole desugaring against our model end-to-end.

fn question_identity(a: Result<u8, u8>) -> Result<u8, u8> {
    let x = a?;
    Ok(x)
}

#[rust_lean_test]
pub fn test_question_propagates_ok() -> bool {
    match question_identity(ok_u8_u8(7)) {
        Ok(v) => v == 7,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_question_propagates_err() -> bool {
    match question_identity(err_u8_u8(3)) {
        Ok(_) => false,
        Err(e) => e == 3,
    }
}

#[rust_lean_test]
pub fn test_expect_err() -> bool {
    err_u8_u8(4).expect_err("expected an error") == 4
}

// ----- methods newly reachable from Lean -------------------------------------

#[rust_lean_test]
pub fn test_is_ok_and_true() -> bool {
    ok_u8_u8(7).is_ok_and(|v| v == 7)
}

#[rust_lean_test]
pub fn test_is_ok_and_false_on_err() -> bool {
    !err_u8_u8(7).is_ok_and(|v| v == 7)
}

#[rust_lean_test]
pub fn test_is_err_and_true() -> bool {
    err_u8_u8(3).is_err_and(|e| e == 3)
}

#[rust_lean_test]
pub fn test_map_ok() -> bool {
    match ok_u8_u8(4).map(|v| v + 1) {
        Ok(v) => v == 5,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_map_leaves_err() -> bool {
    match err_u8_u8(4).map(|v| v + 1) {
        Ok(_) => false,
        Err(e) => e == 4,
    }
}

#[rust_lean_test]
pub fn test_map_or_ok() -> bool {
    ok_u8_u8(4).map_or(0, |v| v + 1) == 5
}

#[rust_lean_test]
pub fn test_map_or_err_uses_default() -> bool {
    err_u8_u8(4).map_or(9, |v| v + 1) == 9
}

#[rust_lean_test]
pub fn test_map_or_else_err_branch() -> bool {
    err_u8_u8(4).map_or_else(|e| e + 1, |v| v) == 5
}

#[rust_lean_test]
pub fn test_unwrap_or_else_uses_err() -> bool {
    err_u8_u8(4).unwrap_or_else(|e| e + 1) == 5
}

#[rust_lean_test]
pub fn test_and_then_chains() -> bool {
    match ok_u8_u8(4).and_then(|v| ok_u8_u8(v + 1)) {
        Ok(v) => v == 5,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_and_then_short_circuits() -> bool {
    match err_u8_u8(4).and_then(|v| ok_u8_u8(v + 1)) {
        Ok(_) => false,
        Err(e) => e == 4,
    }
}

#[rust_lean_test]
pub fn test_or_else_recovers() -> bool {
    match err_u8_u8(4).or_else(|e| ok_u8_u8(e + 1)) {
        Ok(v) => v == 5,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_inspect_returns_self() -> bool {
    match ok_u8_u8(4).inspect(|_| ()) {
        Ok(v) => v == 4,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_inspect_err_returns_self() -> bool {
    match err_u8_u8(4).inspect_err(|_| ()) {
        Ok(_) => false,
        Err(e) => e == 4,
    }
}

// ----- dictionary-applying tests ---------------------------------------------

#[rust_lean_test]
pub fn test_eq_ok_goes_through_the_dictionary() -> bool {
    let a: Result<Keyed, u8> = Ok(keyed(5, 1));
    let b: Result<Keyed, u8> = Ok(keyed(5, 2));
    a == b
}

#[rust_lean_test]
pub fn test_eq_err_goes_through_the_dictionary() -> bool {
    let a: Result<u8, Keyed> = Err(keyed(5, 1));
    let b: Result<u8, Keyed> = Err(keyed(5, 2));
    a == b
}

#[rust_lean_test]
pub fn test_eq_ok_differing_keys() -> bool {
    let a: Result<Keyed, u8> = Ok(keyed(5, 1));
    let b: Result<Keyed, u8> = Ok(keyed(6, 1));
    (a == b) == false
}

// The mismatch arm never reaches either dictionary.
#[rust_lean_test]
pub fn test_eq_ok_vs_err() -> bool {
    let a: Result<Keyed, Keyed> = Ok(keyed(5, 1));
    let b: Result<Keyed, Keyed> = Err(keyed(5, 1));
    (a == b) == false
}

#[rust_lean_test]
pub fn test_clone_ok_applies_element_clone() -> bool {
    let a: Result<Bumped, Bumped> = Ok(Bumped(1));
    match a.clone() {
        Ok(b) => b.0 == 2,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_clone_err_applies_element_clone() -> bool {
    let a: Result<Bumped, Bumped> = Err(Bumped(1));
    match a.clone() {
        Err(b) => b.0 == 2,
        Ok(_) => false,
    }
}

// ----- unwrap_unchecked ------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_unchecked_ok_zero() -> bool {
    unsafe { ok_u8_u8(0).unwrap_unchecked() == 0 }
}

#[rust_lean_test]
pub fn test_unwrap_unchecked_ok_max() -> bool {
    unsafe { ok_u8_u8(u8::MAX).unwrap_unchecked() == u8::MAX }
}

#[rust_lean_test]
pub fn test_unwrap_unchecked_ok_mid() -> bool {
    unsafe { ok_u8_u8(7).unwrap_unchecked() == 7 }
}

// ----- unwrap_err_unchecked --------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_err_unchecked_err_zero() -> bool {
    unsafe { err_u8_u8(0).unwrap_err_unchecked() == 0 }
}

#[rust_lean_test]
pub fn test_unwrap_err_unchecked_err_max() -> bool {
    unsafe { err_u8_u8(u8::MAX).unwrap_err_unchecked() == u8::MAX }
}

#[rust_lean_test]
pub fn test_unwrap_err_unchecked_err_mid() -> bool {
    unsafe { err_u8_u8(7).unwrap_err_unchecked() == 7 }
}

// ----- iter / into_iter ------------------------------------------------------

#[rust_lean_test]
pub fn test_iter_ok_yields_the_value() -> bool {
    let r = ok_u8_u8(7);
    let mut it = r.iter();
    it.next() == Some(&7) && it.next().is_none()
}

#[rust_lean_test]
pub fn test_iter_err_is_empty() -> bool {
    err_u8_u8(u8::MAX).iter().next().is_none()
}

#[rust_lean_test]
pub fn test_into_iter_ok() -> bool {
    let mut it = ok_u8_u8(0).into_iter();
    it.next() == Some(0) && it.next().is_none()
}

#[rust_lean_test]
pub fn test_into_iter_err() -> bool {
    err_u8_u8(0).into_iter().next().is_none()
}

// ----- as_deref / as_deref_mut / copied --------------------------------------

#[rust_lean_test]
pub fn test_as_deref_ok() -> bool {
    let v: u8 = 7;
    let r: Result<&u8, u8> = Ok(&v);
    r.as_deref() == Ok(&7)
}

#[rust_lean_test]
pub fn test_as_deref_err() -> bool {
    let r: Result<&u8, u8> = Err(u8::MAX);
    r.as_deref() == Err(&u8::MAX)
}

#[rust_lean_test]
pub fn test_copied_ok() -> bool {
    let v: u8 = 0;
    let r: Result<&u8, u8> = Ok(&v);
    r.copied() == Ok(0)
}

fn ok_copy_bumped_ref(b: &CopyBumped) -> Result<&CopyBumped, u8> {
    Ok(b)
}

#[rust_lean_test]
pub fn test_copied_ok_does_not_clone() -> bool {
    let v = CopyBumped(0);
    match ok_copy_bumped_ref(&v).copied() {
        Ok(c) => c.0 == 0,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_copied_err() -> bool {
    let r: Result<&u8, u8> = Err(u8::MAX);
    r.copied() == Err(u8::MAX)
}

// Rust-only: the model has no `DerefMut for &mut T` in Lean, whose reborrow aeneas
// mistranslates.
#[cfg(test)]
mod as_deref_mut {
    #[test]
    fn test_as_deref_mut_ok_mutates_through() {
        let mut v: u8 = 0;
        let mut r: Result<&mut u8, u8> = Ok(&mut v);
        if let Ok(inner) = r.as_deref_mut() {
            *inner = u8::MAX;
        }
        assert!(v == u8::MAX);
    }

    #[test]
    fn test_as_deref_mut_err() {
        let mut r: Result<&mut u8, u8> = Err(3);
        assert!(r.as_deref_mut().is_err());
    }
}
