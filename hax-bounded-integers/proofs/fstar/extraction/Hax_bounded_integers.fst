module Hax_bounded_integers
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

///Bounded i128 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedI128 (v_MIN v_MAX: i128) = x: i128{x >=. v_MIN && x <=. v_MAX}

///Bounded i16 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedI16 (v_MIN v_MAX: i16) = x: i16{x >=. v_MIN && x <=. v_MAX}

///Bounded i32 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedI32 (v_MIN v_MAX: i32) = x: i32{x >=. v_MIN && x <=. v_MAX}

///Bounded i64 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedI64 (v_MIN v_MAX: i64) = x: i64{x >=. v_MIN && x <=. v_MAX}

///Bounded i8 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedI8 (v_MIN v_MAX: i8) = x: i8{x >=. v_MIN && x <=. v_MAX}

///Bounded isize integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedIsize (v_MIN v_MAX: isize) = x: isize{x >=. v_MIN && x <=. v_MAX}

///Bounded u128 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedU128 (v_MIN v_MAX: u128) = x: u128{x >=. v_MIN && x <=. v_MAX}

///Bounded u16 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedU16 (v_MIN v_MAX: u16) = x: u16{x >=. v_MIN && x <=. v_MAX}

///Bounded u32 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedU32 (v_MIN v_MAX: u32) = x: u32{x >=. v_MIN && x <=. v_MAX}

///Bounded u64 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedU64 (v_MIN v_MAX: u64) = x: u64{x >=. v_MIN && x <=. v_MAX}

///Bounded u8 integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedU8 (v_MIN v_MAX: u8) = x: u8{x >=. v_MIN && x <=. v_MAX}

///Bounded usize integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.
let t_BoundedUsize (v_MIN v_MAX: usize) = x: usize{x >=. v_MIN && x <=. v_MAX}
