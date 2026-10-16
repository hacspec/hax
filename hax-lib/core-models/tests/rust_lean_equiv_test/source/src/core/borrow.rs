//! Equivalence tests for `core::borrow::*`.

use core::borrow::{Borrow, BorrowMut};
use rust_lean_test_macro::rust_lean_test;

// ----- Borrow::borrow ---------------------------------------------------------

#[rust_lean_test]
pub fn test_borrow_u8_max() -> bool {
    *Borrow::<u8>::borrow(&u8::MAX) == u8::MAX
}

#[rust_lean_test]
pub fn test_borrow_i32_min() -> bool {
    *Borrow::<i32>::borrow(&i32::MIN) == i32::MIN
}

#[rust_lean_test]
pub fn test_borrow_bool_false() -> bool {
    *Borrow::<bool>::borrow(&false) == false
}

// ----- BorrowMut::borrow_mut: read back ---------------------------------------

#[rust_lean_test]
pub fn test_borrow_mut_u8_zero() -> bool {
    let mut x: u8 = 0;
    *BorrowMut::<u8>::borrow_mut(&mut x) == 0u8
}

#[rust_lean_test]
pub fn test_borrow_mut_u8_max() -> bool {
    let mut x: u8 = u8::MAX;
    *BorrowMut::<u8>::borrow_mut(&mut x) == u8::MAX
}

#[rust_lean_test]
pub fn test_borrow_mut_i8_min() -> bool {
    let mut x: i8 = i8::MIN;
    *BorrowMut::<i8>::borrow_mut(&mut x) == i8::MIN
}

#[rust_lean_test]
pub fn test_borrow_mut_bool_true() -> bool {
    let mut x: bool = true;
    *BorrowMut::<bool>::borrow_mut(&mut x) == true
}

// ----- BorrowMut::borrow_mut: write through -----------------------------------

#[rust_lean_test]
pub fn test_borrow_mut_u8_write_through() -> bool {
    let mut x: u8 = 0;
    *BorrowMut::<u8>::borrow_mut(&mut x) = 42;
    x == 42u8
}

#[rust_lean_test]
pub fn test_borrow_mut_u32_write_max() -> bool {
    let mut x: u32 = 7;
    *BorrowMut::<u32>::borrow_mut(&mut x) = u32::MAX;
    x == u32::MAX
}

#[rust_lean_test]
pub fn test_borrow_mut_i32_write_min() -> bool {
    let mut x: i32 = 0;
    *BorrowMut::<i32>::borrow_mut(&mut x) = i32::MIN;
    x == i32::MIN
}
