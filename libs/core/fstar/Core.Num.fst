module Core.Num
open Core.Types
open FStar.Integers
open FStar.UInt32

let wrapping_add_under_impl_8 (x: u32) (y: u32): u32 = add_underspec x y
let rotate_left_under_impl_8 x y = x
