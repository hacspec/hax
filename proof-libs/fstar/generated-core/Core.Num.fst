module Core.Num
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Core.Ops.Arith

let impl_4__MAX: Core.Primitive.t_u128 =
  Core.Primitive.C_u128 Core.Int.f_MAX <: Core.Primitive.t_u128

let impl_4__MIN: Core.Primitive.t_u128 =
  Core.Primitive.C_u128 Core.Int.f_MIN <: Core.Primitive.t_u128

let impl_1__MAX: Core.Primitive.t_u16 = Core.Primitive.C_u16 Core.Int.f_MAX <: Core.Primitive.t_u16

let impl_1__MIN: Core.Primitive.t_u16 = Core.Primitive.C_u16 Core.Int.f_MIN <: Core.Primitive.t_u16

let impl__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Int.impl_21__BITS <: Core.Primitive.t_u32

let impl_1__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Int.impl_48__BITS <: Core.Primitive.t_u32

let impl_2__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Int.impl_75__BITS <: Core.Primitive.t_u32

let impl_2__MAX: Core.Primitive.t_u32 = Core.Primitive.C_u32 Core.Int.f_MAX <: Core.Primitive.t_u32

let impl_2__MIN: Core.Primitive.t_u32 = Core.Primitive.C_u32 Core.Int.f_MIN <: Core.Primitive.t_u32

let impl_3__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Int.impl_102__BITS <: Core.Primitive.t_u32

let impl_4__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Int.impl_129__BITS <: Core.Primitive.t_u32

let impl_5__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Int.impl_102__BITS <: Core.Primitive.t_u32

let impl_3__MAX: Core.Primitive.t_u64 = Core.Primitive.C_u64 Core.Int.f_MAX <: Core.Primitive.t_u64

let impl_3__MIN: Core.Primitive.t_u64 = Core.Primitive.C_u64 Core.Int.f_MIN <: Core.Primitive.t_u64

let impl__MAX: Core.Primitive.t_u8 = Core.Primitive.C_u8 Core.Int.f_MAX <: Core.Primitive.t_u8

let impl__MIN: Core.Primitive.t_u8 = Core.Primitive.C_u8 Core.Int.f_MIN <: Core.Primitive.t_u8

let impl_5__MAX: Core.Primitive.t_usize =
  Core.Primitive.C_usize Core.Int.f_MAX <: Core.Primitive.t_usize

let impl_5__MIN: Core.Primitive.t_usize =
  Core.Primitive.C_usize Core.Int.f_MIN <: Core.Primitive.t_usize

let impl__overflowing_add (self rhs: Core.Primitive.t_u8) : (Core.Primitive.t_u8 & bool) =
  Core.Intrinsics.add_with_overflow_u8 self rhs

let impl_1__overflowing_add (self rhs: Core.Primitive.t_u16) : (Core.Primitive.t_u16 & bool) =
  Core.Intrinsics.add_with_overflow_u16 self rhs

let impl_2__overflowing_add (self rhs: Core.Primitive.t_u32) : (Core.Primitive.t_u32 & bool) =
  Core.Intrinsics.add_with_overflow_u32 self rhs

let impl_3__overflowing_add (self rhs: Core.Primitive.t_u64) : (Core.Primitive.t_u64 & bool) =
  Core.Intrinsics.add_with_overflow_u64 self rhs

let impl_4__overflowing_add (self rhs: Core.Primitive.t_u128) : (Core.Primitive.t_u128 & bool) =
  Core.Intrinsics.add_with_overflow_u128 self rhs

let impl_5__overflowing_add (self rhs: Core.Primitive.t_usize) : (Core.Primitive.t_usize & bool) =
  Core.Intrinsics.add_with_overflow_usize self rhs

let impl__wrapping_add (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Intrinsics.wrapping_add_u8 self rhs

let impl__wrapping_mul (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Intrinsics.wrapping_mul_u8 self rhs

let impl_1__wrapping_add (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Intrinsics.wrapping_add_u16 self rhs

let impl_1__wrapping_mul (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Intrinsics.wrapping_mul_u16 self rhs

let impl_2__wrapping_add (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Intrinsics.wrapping_add_u32 self rhs

let impl_2__wrapping_mul (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Intrinsics.wrapping_mul_u32 self rhs

let impl_3__wrapping_add (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Intrinsics.wrapping_add_u64 self rhs

let impl_3__wrapping_mul (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Intrinsics.wrapping_mul_u64 self rhs

let impl_4__wrapping_add (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Intrinsics.wrapping_add_u128 self rhs

let impl_4__wrapping_mul (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Intrinsics.wrapping_mul_u128 self rhs

let impl_5__wrapping_add (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Intrinsics.wrapping_add_usize self rhs

let impl_5__wrapping_mul (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Intrinsics.wrapping_mul_usize self rhs

let impl__wrapping_sub (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Intrinsics.wrapping_sub_u8 self rhs

let impl__wrapping_neg (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  impl__wrapping_sub (Core.Primitive.C_u8 Core.Int.f_ZERO <: Core.Primitive.t_u8) self

let impl_1__wrapping_sub (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Intrinsics.wrapping_sub_u16 self rhs

let impl_1__wrapping_neg (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  impl_1__wrapping_sub (Core.Primitive.C_u16 Core.Int.f_ZERO <: Core.Primitive.t_u16) self

let impl_2__wrapping_sub (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Intrinsics.wrapping_sub_u32 self rhs

let impl_2__wrapping_neg (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  impl_2__wrapping_sub (Core.Primitive.C_u32 Core.Int.f_ZERO <: Core.Primitive.t_u32) self

let impl_3__wrapping_sub (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Intrinsics.wrapping_sub_u64 self rhs

let impl_3__wrapping_neg (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  impl_3__wrapping_sub (Core.Primitive.C_u64 Core.Int.f_ZERO <: Core.Primitive.t_u64) self

let impl_4__wrapping_sub (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Intrinsics.wrapping_sub_u128 self rhs

let impl_4__wrapping_neg (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  impl_4__wrapping_sub (Core.Primitive.C_u128 Core.Int.f_ZERO <: Core.Primitive.t_u128) self

let impl_5__wrapping_sub (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Intrinsics.wrapping_sub_usize self rhs

let impl_5__wrapping_neg (self: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  impl_5__wrapping_sub (Core.Primitive.C_usize Core.Int.f_ZERO <: Core.Primitive.t_usize) self

let impl__wrapping_rem (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self %! rhs

let impl__wrapping_rem_euclid (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self %! rhs

let impl__wrapping_div (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self /! rhs

let impl__wrapping_div_euclid (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self /! rhs

let impl_1__wrapping_rem (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self %! rhs

let impl_1__wrapping_rem_euclid (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  self %! rhs

let impl_1__wrapping_div (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self /! rhs

let impl_1__wrapping_div_euclid (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  self /! rhs

let impl_2__wrapping_rem (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self %! rhs

let impl_2__wrapping_rem_euclid (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  self %! rhs

let impl_2__wrapping_div (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self /! rhs

let impl_2__wrapping_div_euclid (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  self /! rhs

let impl_3__wrapping_rem (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self %! rhs

let impl_3__wrapping_rem_euclid (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  self %! rhs

let impl_3__wrapping_div (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self /! rhs

let impl_3__wrapping_div_euclid (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  self /! rhs

let impl_4__wrapping_rem (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self %! rhs

let impl_4__wrapping_rem_euclid (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  self %! rhs

let impl_4__wrapping_div (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self /! rhs

let impl_4__wrapping_div_euclid (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  self /! rhs

let impl_5__wrapping_rem (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize = self %! rhs

let impl_5__wrapping_rem_euclid (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  self %! rhs

let impl_5__wrapping_div (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize = self /! rhs

let impl_5__wrapping_div_euclid (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  self /! rhs
