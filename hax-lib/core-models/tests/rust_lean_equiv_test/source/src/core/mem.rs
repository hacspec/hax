//! Equivalence tests for `core::mem::*`.
//!
//! `swap` and `replace` carry `#[cfg_attr(hax_backend_lean, hax_lib::exclude)]`
//! so Aeneas does not extract the Rust std bodies; instead the name map routes
//! them to hand-written Lean definitions. The Rust side of each test calls std
//! directly — if the manual Lean def disagrees with std on a given input, the
//! generated `#guard` fails the Lean build.

use rust_lean_test_macro::rust_lean_test;

// ----- mem::swap (manually defined in Lean, not extracted) ------------------

#[rust_lean_test]
pub fn test_swap_u8_distinct() -> bool {
    let mut a: u8 = 1;
    let mut b: u8 = 2;
    core::mem::swap(&mut a, &mut b);
    a == 2 && b == 1
}

#[rust_lean_test]
pub fn test_swap_u8_equal() -> bool {
    let mut a: u8 = 7;
    let mut b: u8 = 7;
    core::mem::swap(&mut a, &mut b);
    a == 7 && b == 7
}

#[rust_lean_test]
pub fn test_swap_u8_min_max() -> bool {
    let mut a: u8 = u8::MIN;
    let mut b: u8 = u8::MAX;
    core::mem::swap(&mut a, &mut b);
    a == u8::MAX && b == u8::MIN
}

#[rust_lean_test]
pub fn test_swap_u32_distinct() -> bool {
    let mut a: u32 = 100;
    let mut b: u32 = 200;
    core::mem::swap(&mut a, &mut b);
    a == 200 && b == 100
}

#[rust_lean_test]
pub fn test_swap_u32_min_max() -> bool {
    let mut a: u32 = u32::MIN;
    let mut b: u32 = u32::MAX;
    core::mem::swap(&mut a, &mut b);
    a == u32::MAX && b == u32::MIN
}

#[rust_lean_test]
pub fn test_swap_tuple_u32() -> bool {
    let mut a: (u32, u32) = (1, 2);
    let mut b: (u32, u32) = (3, 4);
    core::mem::swap(&mut a, &mut b);
    a.0 == 3 && a.1 == 4 && b.0 == 1 && b.1 == 2
}

// ----- mem::replace (manually defined in Lean, not extracted) ---------------

#[rust_lean_test]
pub fn test_replace_u8_returns_old() -> bool {
    let mut dst: u8 = 5;
    let old = core::mem::replace(&mut dst, 9);
    old == 5
}

#[rust_lean_test]
pub fn test_replace_u8_leaves_new() -> bool {
    let mut dst: u8 = 5;
    let _ = core::mem::replace(&mut dst, 9);
    dst == 9
}

#[rust_lean_test]
pub fn test_replace_u8_min_max() -> bool {
    let mut dst: u8 = u8::MIN;
    let old = core::mem::replace(&mut dst, u8::MAX);
    old == u8::MIN && dst == u8::MAX
}

#[rust_lean_test]
pub fn test_replace_u8_equal_values() -> bool {
    let mut dst: u8 = 3;
    let old = core::mem::replace(&mut dst, 3);
    old == 3 && dst == 3
}

#[rust_lean_test]
pub fn test_replace_tuple_returns_old() -> bool {
    let mut dst: (u32, u32) = (1, 2);
    let old = core::mem::replace(&mut dst, (3, 4));
    old.0 == 1 && old.1 == 2
}

#[rust_lean_test]
pub fn test_replace_tuple_leaves_new() -> bool {
    let mut dst: (u32, u32) = (1, 2);
    let _ = core::mem::replace(&mut dst, (3, 4));
    dst.0 == 3 && dst.1 == 4
}

#[rust_lean_test]
pub fn test_replace_option_some_with_none() -> bool {
    let mut dst: Option<u8> = Some(7);
    let _old = core::mem::replace(&mut dst, crate::helpers::none_u8());
    dst.is_none()
}

#[rust_lean_test]
pub fn test_replace_option_none_with_some() -> bool {
    let mut dst: Option<u8> = crate::helpers::none_u8();
    let old = core::mem::replace(&mut dst, Some(42));
    old.is_none() && dst == Some(42)
}

#[rust_lean_test]
pub fn test_replace_option_some_with_some() -> bool {
    let mut dst: Option<u8> = Some(1);
    let old = core::mem::replace(&mut dst, Some(2));
    old == Some(1) && dst == Some(2)
}

// ----- mem::copy -------------------------------------------------------------

// Integers only: the model has no other `Copy` impls.

#[rust_lean_test]
pub fn test_copy_u8_zero() -> bool {
    core::mem::copy(&0u8) == 0
}

#[rust_lean_test]
pub fn test_copy_u8_max() -> bool {
    core::mem::copy(&u8::MAX) == u8::MAX
}

#[rust_lean_test]
pub fn test_copy_i8_min() -> bool {
    core::mem::copy(&i8::MIN) == i8::MIN
}

#[rust_lean_test]
pub fn test_copy_u32_max() -> bool {
    core::mem::copy(&u32::MAX) == u32::MAX
}

#[rust_lean_test]
pub fn test_copy_i32_min() -> bool {
    core::mem::copy(&i32::MIN) == i32::MIN
}

#[rust_lean_test]
pub fn test_copy_usize_zero() -> bool {
    core::mem::copy(&0usize) == 0
}

#[rust_lean_test]
pub fn test_copy_u64_max() -> bool {
    core::mem::copy(&u64::MAX) == u64::MAX
}

// ----- ManuallyDrop ----------------------------------------------------------

#[rust_lean_test]
pub fn test_manually_drop_into_inner_u8() -> bool {
    core::mem::ManuallyDrop::into_inner(core::mem::ManuallyDrop::new(7u8)) == 7
}

#[rust_lean_test]
pub fn test_manually_drop_into_inner_u8_max() -> bool {
    core::mem::ManuallyDrop::into_inner(core::mem::ManuallyDrop::new(u8::MAX)) == u8::MAX
}

#[rust_lean_test]
pub fn test_manually_drop_into_inner_i32_min() -> bool {
    core::mem::ManuallyDrop::into_inner(core::mem::ManuallyDrop::new(i32::MIN)) == i32::MIN
}

#[rust_lean_test]
pub fn test_manually_drop_into_inner_tuple() -> bool {
    let t = core::mem::ManuallyDrop::into_inner(core::mem::ManuallyDrop::new((1u32, 2u32)));
    t.0 == 1 && t.1 == 2
}

#[rust_lean_test]
pub fn test_manually_drop_into_inner_option_none() -> bool {
    core::mem::ManuallyDrop::into_inner(core::mem::ManuallyDrop::new(crate::helpers::none_u8()))
        .is_none()
}

// `u8` is `Copy`: the model's slot would drop a value with a destructor again.
#[rust_lean_test]
pub fn test_manually_drop_take_u8() -> bool {
    let mut slot = core::mem::ManuallyDrop::new(7u8);
    let v = unsafe { core::mem::ManuallyDrop::take(&mut slot) };
    v == 7
}

#[rust_lean_test]
pub fn test_manually_drop_take_i32_min() -> bool {
    let mut slot = core::mem::ManuallyDrop::new(i32::MIN);
    let v = unsafe { core::mem::ManuallyDrop::take(&mut slot) };
    v == i32::MIN
}

// Sound: `u8` has no destructor.
#[rust_lean_test]
pub fn test_manually_drop_drop_leaves_u8() -> bool {
    let mut slot = core::mem::ManuallyDrop::new(7u8);
    unsafe { core::mem::ManuallyDrop::drop(&mut slot) };
    core::mem::ManuallyDrop::into_inner(slot) == 7
}

// ----- Rust-only: DropGuard --------------------------------------------------

// TODO(closure-extraction): `DropGuard::new` takes a closure.
#[cfg(test)]
mod drop_guard {
    #[test]
    fn test_dismiss_returns_inner() {
        let guard = core::mem::DropGuard::new(5u8, |_: u8| ());
        assert_eq!(core::mem::DropGuard::into_inner(guard), 5);
    }

    #[test]
    fn test_dismiss_does_not_run_the_closure() {
        let mut ran = false;
        {
            let guard = core::mem::DropGuard::new(1u8, |_: u8| ran = true);
            let _ = core::mem::DropGuard::into_inner(guard);
        }
        assert!(!ran);
    }
}
