//! Equivalence tests for `core::ops::*`.
//!
//! Covers `add_assign`/`sub_assign` on `u8`, `ControlFlow`, `Bound` and the range types.
//!
//! On the Rust side we use the `+=` / `-=` operators (which dispatch
//! through `AddAssign` / `SubAssign`); on the Lean side Aeneas
//! extracts the same operations against the model's impls.
//!
//! All values are kept inside the precondition ranges (no overflow,
//! lhs >= rhs).
//!
//! TODO(closure-extraction): `ControlFlow::map_*` and `Bound::map` are untested.

use crate::helpers;
use core::ops::{Bound, RangeBounds, RangeInclusive};
use rust_lean_test_macro::rust_lean_test;

// =============================================================================
// AddAssign on u8 (precondition: x + y <= u8::MAX, mirrored from
// the proptest's `0u8..128` range bound on both operands)
// =============================================================================

#[rust_lean_test]
pub fn test_add_assign_u8_zero_zero() -> bool {
    let mut x: u8 = 0;
    x += 0u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_zero_plus_one() -> bool {
    let mut x: u8 = 0;
    x += 1u8;
    x == 1u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_mid() -> bool {
    let mut x: u8 = 42;
    x += 58u8;
    x == 100u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_boundary() -> bool {
    // The proptest constrains both operands to `0..128`, so 127 + 127
    // is the largest sum we can express (= 254, just under u8::MAX).
    let mut x: u8 = 127;
    x += 127u8;
    x == 254u8
}

#[rust_lean_test]
pub fn test_add_assign_u8_lhs_zero() -> bool {
    let mut x: u8 = 0;
    x += 127u8;
    x == 127u8
}

// =============================================================================
// SubAssign on u8 (precondition: lhs >= rhs)
// =============================================================================

#[rust_lean_test]
pub fn test_sub_assign_u8_zero_zero() -> bool {
    let mut x: u8 = 0;
    x -= 0u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_self() -> bool {
    let mut x: u8 = 42;
    x -= 42u8;
    x == 0u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_mid() -> bool {
    let mut x: u8 = 100;
    x -= 42u8;
    x == 58u8
}

#[rust_lean_test]
pub fn test_sub_assign_u8_max_minus_zero() -> bool {
    let mut x: u8 = u8::MAX;
    x -= 0u8;
    x == u8::MAX
}

#[rust_lean_test]
pub fn test_sub_assign_u8_max_minus_one() -> bool {
    let mut x: u8 = u8::MAX;
    x -= 1u8;
    x == 254u8
}

// =============================================================================
// Ranges
// =============================================================================

#[rust_lean_test]
pub fn test_range_inclusive_into_inner() -> bool {
    (2u8..=5).into_inner() == (2u8, 5u8)
}

#[rust_lean_test]
pub fn test_range_inclusive_accessors() -> bool {
    let r = 1usize..=3;
    *r.start() == 1 && *r.end() == 3
}

#[rust_lean_test]
pub fn test_range_inclusive_contains() -> bool {
    let r = 2u8..=5;
    r.contains(&2) && r.contains(&5) && !r.contains(&1) && !r.contains(&6)
}

#[rust_lean_test]
pub fn test_range_inclusive_is_empty() -> bool {
    !(2u8..=2).is_empty() && (3u8..=2).is_empty()
}

fn contains_via_bounds<R: core::ops::RangeBounds<u8>>(r: R, x: u8) -> bool {
    r.contains(&x)
}

#[rust_lean_test]
pub fn test_range_bounds_contains() -> bool {
    use core::ops::Bound;
    contains_via_bounds(2u8..5, 4)
        && !contains_via_bounds(2u8..5, 5)
        && contains_via_bounds(..=5u8, 5)
        && !contains_via_bounds(3u8.., 2)
        && contains_via_bounds(.., 0)
        && !contains_via_bounds((Bound::Excluded(2u8), Bound::Unbounded), 2)
}

// =============================================================================
// ControlFlow::is_break / is_continue
// =============================================================================

#[rust_lean_test]
pub fn test_control_flow_is_break_on_break() -> bool {
    helpers::control_flow_break_u8(7).is_break() == true
}

#[rust_lean_test]
pub fn test_control_flow_is_break_on_continue() -> bool {
    helpers::control_flow_continue_u8(0).is_break() == false
}

#[rust_lean_test]
pub fn test_control_flow_is_continue_on_continue() -> bool {
    helpers::control_flow_continue_u8(u8::MAX).is_continue() == true
}

#[rust_lean_test]
pub fn test_control_flow_is_continue_on_break() -> bool {
    helpers::control_flow_break_u8(0).is_continue() == false
}

// =============================================================================
// ControlFlow::break_value / continue_value
// =============================================================================

#[rust_lean_test]
pub fn test_control_flow_break_value_on_break() -> bool {
    match helpers::control_flow_break_u8(u8::MAX).break_value() {
        Some(b) => b == u8::MAX,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_control_flow_break_value_on_continue() -> bool {
    match helpers::control_flow_continue_u8(3).break_value() {
        Some(_) => false,
        None => true,
    }
}

#[rust_lean_test]
pub fn test_control_flow_continue_value_on_continue() -> bool {
    match helpers::control_flow_continue_u8(0).continue_value() {
        Some(c) => c == 0u8,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_control_flow_continue_value_on_break() -> bool {
    match helpers::control_flow_break_u8(3).continue_value() {
        Some(_) => false,
        None => true,
    }
}

// =============================================================================
// Bound::as_ref
// =============================================================================

#[rust_lean_test]
pub fn test_bound_as_ref_included() -> bool {
    let b: Bound<u8> = Bound::Included(7);
    match b.as_ref() {
        Bound::Included(x) => *x == 7u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_bound_as_ref_excluded_max() -> bool {
    let b: Bound<u8> = Bound::Excluded(u8::MAX);
    match b.as_ref() {
        Bound::Excluded(x) => *x == u8::MAX,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_bound_as_ref_unbounded() -> bool {
    match helpers::bound_unbounded_u8().as_ref() {
        Bound::Unbounded => true,
        _ => false,
    }
}

// ----- Bound::cloned ---------------------------------------------------------

#[rust_lean_test]
pub fn test_bound_cloned_included() -> bool {
    let x: u8 = 7;
    match Bound::Included(&x).cloned() {
        Bound::Included(v) => v == 7u8,
        _ => false,
    }
}

// =============================================================================
// RangeBounds::start_bound / end_bound
// =============================================================================

#[rust_lean_test]
pub fn test_range_start_bound() -> bool {
    match (3u8..5u8).start_bound() {
        Bound::Included(x) => *x == 3u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_end_bound() -> bool {
    match (3u8..5u8).end_bound() {
        Bound::Excluded(x) => *x == 5u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_from_start_bound() -> bool {
    match (0u8..).start_bound() {
        Bound::Included(x) => *x == 0u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_from_end_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::end_bound(&(0u8..)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_start_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::start_bound(&(..5u8)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_end_bound() -> bool {
    match (..u8::MAX).end_bound() {
        Bound::Excluded(x) => *x == u8::MAX,
        _ => false,
    }
}

// One `match` per test: combining two makes Aeneas's interpreter fail.
#[rust_lean_test]
pub fn test_range_full_start_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::start_bound(&(..)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_full_end_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::end_bound(&(..)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_inclusive_start_bound() -> bool {
    match RangeInclusive::new(3u8, 5u8).start_bound() {
        Bound::Included(x) => *x == 3u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_inclusive_end_bound_is_included() -> bool {
    match RangeInclusive::new(3u8, 5u8).end_bound() {
        Bound::Included(x) => *x == 5u8,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_inclusive_start_bound_is_unbounded() -> bool {
    match RangeBounds::<u8>::start_bound(&(..=5u8)) {
        Bound::Unbounded => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_range_to_inclusive_end_bound() -> bool {
    match (..=5u8).end_bound() {
        Bound::Included(x) => *x == 5u8,
        _ => false,
    }
}

// =============================================================================
// Range::contains / Range::is_empty
// =============================================================================

#[rust_lean_test]
pub fn test_range_contains_inside() -> bool {
    (3u8..5u8).contains(&4u8) == true
}

#[rust_lean_test]
pub fn test_range_contains_start_is_included() -> bool {
    (3u8..5u8).contains(&3u8) == true
}

#[rust_lean_test]
pub fn test_range_contains_end_is_excluded() -> bool {
    (3u8..5u8).contains(&5u8) == false
}

#[rust_lean_test]
pub fn test_range_contains_below() -> bool {
    (3u8..5u8).contains(&0u8) == false
}

#[rust_lean_test]
pub fn test_range_contains_max() -> bool {
    (0u8..u8::MAX).contains(&u8::MAX) == false
}

#[rust_lean_test]
pub fn test_range_is_empty_nonempty() -> bool {
    (3u8..5u8).is_empty() == false
}

#[rust_lean_test]
pub fn test_range_is_empty_equal_bounds() -> bool {
    (3u8..3u8).is_empty() == true
}

#[rust_lean_test]
pub fn test_range_is_empty_reversed() -> bool {
    (5u8..3u8).is_empty() == true
}

#[rust_lean_test]
pub fn test_range_is_empty_full_u8() -> bool {
    (0u8..u8::MAX).is_empty() == false
}

// =============================================================================
// RangeFrom::contains
// =============================================================================

#[rust_lean_test]
pub fn test_range_from_contains_above() -> bool {
    (3u8..).contains(&4u8) == true
}

#[rust_lean_test]
pub fn test_range_from_contains_start() -> bool {
    (3u8..).contains(&3u8) == true
}

#[rust_lean_test]
pub fn test_range_from_contains_below() -> bool {
    (3u8..).contains(&2u8) == false
}

#[rust_lean_test]
pub fn test_range_from_contains_max() -> bool {
    (0u8..).contains(&u8::MAX) == true
}

// =============================================================================
// RangeTo::contains
// =============================================================================

#[rust_lean_test]
pub fn test_range_to_contains_below() -> bool {
    (..5u8).contains(&4u8) == true
}

#[rust_lean_test]
pub fn test_range_to_contains_end_is_excluded() -> bool {
    (..5u8).contains(&5u8) == false
}

#[rust_lean_test]
pub fn test_range_to_contains_zero() -> bool {
    (..5u8).contains(&0u8) == true
}

#[rust_lean_test]
pub fn test_range_to_contains_nothing_when_end_is_zero() -> bool {
    (..0u8).contains(&0u8) == false
}

// =============================================================================
// RangeToInclusive::contains
// =============================================================================

#[rust_lean_test]
pub fn test_range_to_inclusive_contains_end() -> bool {
    (..=5u8).contains(&5u8) == true
}

#[rust_lean_test]
pub fn test_range_to_inclusive_contains_zero() -> bool {
    (..=0u8).contains(&0u8) == true
}

#[rust_lean_test]
pub fn test_range_to_inclusive_contains_above() -> bool {
    (..=5u8).contains(&6u8) == false
}

// =============================================================================
// RangeInclusive::new / into_inner / contains / is_empty
// =============================================================================

// Not `end`: aeneas leaves a binder named after that Lean keyword unparseable.
#[rust_lean_test]
pub fn test_range_inclusive_new_into_inner() -> bool {
    let (lo, hi) = RangeInclusive::new(3u8, 5u8).into_inner();
    lo == 3u8 && hi == 5u8
}

#[rust_lean_test]
pub fn test_range_inclusive_into_inner_edges() -> bool {
    let (lo, hi) = (0u8..=u8::MAX).into_inner();
    lo == 0u8 && hi == u8::MAX
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_end() -> bool {
    (3u8..=5u8).contains(&5u8) == true
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_start() -> bool {
    (3u8..=5u8).contains(&3u8) == true
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_above() -> bool {
    (3u8..=5u8).contains(&6u8) == false
}

#[rust_lean_test]
pub fn test_range_inclusive_contains_singleton() -> bool {
    (0u8..=0u8).contains(&0u8) == true
}

#[rust_lean_test]
pub fn test_range_inclusive_is_empty_nonempty() -> bool {
    (3u8..=5u8).is_empty() == false
}

#[rust_lean_test]
pub fn test_range_inclusive_is_empty_singleton() -> bool {
    (3u8..=3u8).is_empty() == false
}

#[rust_lean_test]
pub fn test_range_inclusive_is_empty_reversed() -> bool {
    (5u8..=3u8).is_empty() == true
}
