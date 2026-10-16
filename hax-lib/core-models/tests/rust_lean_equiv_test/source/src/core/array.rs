//! Equivalence tests for `[T; N]` (`core::array`) operations.

use crate::helpers::Bumped;
use rust_lean_test_macro::rust_lean_test;

// ----- Index<RangeTo<usize>> -------------------------------------------------

#[rust_lean_test]
pub fn test_index_range_to_zero() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..0] == []
}

#[rust_lean_test]
pub fn test_index_range_to_three() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..3] == [1, 2, 3]
}

#[rust_lean_test]
pub fn test_index_range_to_full() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..8] == [1, 2, 3, 4, 5, 6, 7, 8]
}

// ----- IndexMut --------------------------------------------------------------
//
// The write-back offsets of `<[T; N] as IndexMut<I>>::index_mut` (cryspen/hax#2174).

#[rust_lean_test]
pub fn test_index_mut_range_middle() -> bool {
    let mut a: [u8; 8] = [0; 8];
    a[2..5].copy_from_slice(&[7, 8, 9]);
    a == [0, 0, 7, 8, 9, 0, 0, 0]
}

#[rust_lean_test]
pub fn test_index_mut_range_from() -> bool {
    let mut a: [u8; 4] = [1, 2, 3, 4];
    a[2..].copy_from_slice(&[9, 9]);
    a == [1, 2, 9, 9]
}

#[rust_lean_test]
pub fn test_index_mut_range_to() -> bool {
    let mut a: [u8; 4] = [1, 2, 3, 4];
    a[..2].copy_from_slice(&[9, 9]);
    a == [9, 9, 3, 4]
}

#[rust_lean_test]
pub fn test_index_mut_range_full_reverse() -> bool {
    let mut a: [u8; 4] = [1, 2, 3, 4];
    a[..].reverse();
    a == [4, 3, 2, 1]
}

#[rust_lean_test]
pub fn test_index_mut_range_empty_is_noop() -> bool {
    let mut a: [u8; 4] = [1, 2, 3, 4];
    a[2..2].copy_from_slice(&[]);
    a == [1, 2, 3, 4]
}

// ----- PartialEq -------------------------------------------------------------

#[rust_lean_test]
pub fn test_eq_same() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let b: [u8; 4] = [1, 2, 3, 4];
    a == b
}

#[rust_lean_test]
pub fn test_eq_different_last() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let b: [u8; 4] = [1, 2, 3, 5];
    (a == b) == false
}

#[rust_lean_test]
pub fn test_eq_different_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let b: [u8; 4] = [0, 2, 3, 4];
    (a == b) == false
}

#[rust_lean_test]
pub fn test_eq_all_zeros() -> bool {
    let a: [u8; 4] = [0, 0, 0, 0];
    let b: [u8; 4] = [0, 0, 0, 0];
    a == b
}

#[rust_lean_test]
pub fn test_from_fn_identity() -> bool {
    let a: [u8; 4] = core::array::from_fn(|i| i as u8);
    a == [0, 1, 2, 3]
}

// ----- map / each_ref --------------------------------------------------------

#[rust_lean_test]
pub fn test_map_add_one() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.map(|x| x + 1) == [2, 3, 4, 5]
}

#[rust_lean_test]
pub fn test_each_ref_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let refs: [&u8; 4] = a.each_ref();
    *refs[0] == 1
}

// ----- Clone for [T; N] ------------------------------------------------------

#[rust_lean_test]
pub fn test_array_clone_applies_element_clone() -> bool {
    let a = [Bumped(1), Bumped(2)];
    let b = a.clone();
    b[0].0 == 2 && b[1].0 == 3
}

// `clone_from` clones element-wise, so the receiver's values do not survive.
#[rust_lean_test]
pub fn test_array_clone_from_applies_element_clone() -> bool {
    let mut dst = [Bumped(10), Bumped(20)];
    let src = [Bumped(1), Bumped(2)];
    dst.clone_from(&src);
    dst[0].0 == 2 && dst[1].0 == 3
}

// ----- as_slice / as_mut_slice -----------------------------------------------

// No model impl for `&[T] == [U; N]`, hence `len` and indexing.
#[rust_lean_test]
pub fn test_as_slice_full() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let s = a.as_slice();
    s.len() == 4 && s[0] == 1 && s[3] == 4
}

#[rust_lean_test]
pub fn test_as_slice_empty() -> bool {
    let a: [u8; 0] = [];
    a.as_slice().len() == 0
}

#[rust_lean_test]
pub fn test_as_mut_slice_fill() -> bool {
    let mut a: [u8; 4] = [1, 2, 3, 4];
    a.as_mut_slice().fill(7);
    a == [7, 7, 7, 7]
}

#[rust_lean_test]
pub fn test_as_mut_slice_swap_ends() -> bool {
    let mut a: [u8; 3] = [1, 2, u8::MAX];
    a.as_mut_slice().swap(0, 2);
    a == [u8::MAX, 2, 1]
}

#[rust_lean_test]
pub fn test_as_mut_slice_empty() -> bool {
    let mut a: [u8; 0] = [];
    a.as_mut_slice().len() == 0
}

// ----- from_ref / from_mut ---------------------------------------------------

#[rust_lean_test]
pub fn test_from_ref_zero() -> bool {
    *core::array::from_ref(&0u8) == [0u8]
}

#[rust_lean_test]
pub fn test_from_ref_max() -> bool {
    *core::array::from_ref(&u8::MAX) == [u8::MAX]
}

#[rust_lean_test]
pub fn test_from_mut_writes_through() -> bool {
    let mut x = 1u8;
    core::array::from_mut(&mut x).as_mut_slice().fill(u8::MAX);
    x == u8::MAX
}

#[rust_lean_test]
pub fn test_from_mut_writes_zero() -> bool {
    let mut x = u8::MAX;
    core::array::from_mut(&mut x).as_mut_slice().fill(0);
    x == 0
}

// ----- IntoIter --------------------------------------------------------------

#[allow(deprecated)]
#[rust_lean_test]
pub fn test_into_iter_new_first() -> bool {
    let mut it = core::array::IntoIter::new([1u8, 2, 3]);
    match it.next() {
        Some(x) => x == 1u8,
        None => false,
    }
}

#[allow(deprecated)]
#[rust_lean_test]
pub fn test_into_iter_new_empty() -> bool {
    let mut it = core::array::IntoIter::new([0u8; 0]);
    it.next().is_none()
}

#[allow(deprecated)]
#[rust_lean_test]
pub fn test_into_iter_as_slice_untouched() -> bool {
    let it = core::array::IntoIter::new([1u8, 2, 3]);
    let s = it.as_slice();
    s.len() == 3 && s[0] == 1 && s[2] == 3
}

#[allow(deprecated)]
#[rust_lean_test]
pub fn test_into_iter_as_slice_after_next() -> bool {
    let mut it = core::array::IntoIter::new([1u8, 2, 3]);
    it.next();
    let s = it.as_slice();
    s.len() == 2 && s[0] == 2 && s[1] == 3
}

#[allow(deprecated)]
#[rust_lean_test]
pub fn test_into_iter_as_mut_slice_fill() -> bool {
    let mut it = core::array::IntoIter::new([1u8, 2, 3]);
    it.as_mut_slice().fill(9);
    let s = it.as_slice();
    s.len() == 3 && s[0] == 9 && s[2] == 9
}

#[rust_lean_test]
pub fn test_into_iter_empty_yields_nothing() -> bool {
    let mut it = core::array::IntoIter::<u8, 3>::empty();
    it.next().is_none()
}
