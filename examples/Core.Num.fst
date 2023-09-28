module Core.Num
open Core.Types
open FStar.Integers
open FStar.UInt32

let wrapping_add_under_impl_8 (x: u32) (y: u32): u32 = add_underspec x y
let rotate_left_under_impl_8 x y = x
let from_le_bytes_under_impl_8: array u8 4sz -> u32 = magic ()
let from_be_bytes_under_impl_8: array u8 4sz -> u32 = magic ()
let to_le_bytes_under_impl_8: u32 -> array u8 4sz = magic ()
let to_be_bytes_under_impl_8: u32 -> array u8 4sz = magic ()
let rotate_right_under_impl_8: u32 -> u32 -> u32 = magic ()


open FStar.UInt64
let wrapping_add_under_impl_9 (x: u64) (y: u64): u64 = add_underspec x y
let rotate_left_under_impl_9 x y = x
let from_le_bytes_under_impl_9: array u8 8sz -> u64 = magic ()
let from_be_bytes_under_impl_9: array u8 8sz -> u64 = magic ()
let to_le_bytes_under_impl_9: u64 -> array u8 8sz = magic ()
let to_be_bytes_under_impl_9: u64 -> array u8 8sz = magic ()
let rotate_right_under_impl_9: u64 -> u64 -> u64 = magic ()


open FStar.UInt128
let wrapping_add_under_impl_10 (x: u128) (y: u128): u128 = add_underspec x y
let rotate_left_under_impl_10 x y = x
let from_le_bytes_under_impl_10: array u8 16sz -> u128 = magic ()
let from_be_bytes_under_impl_10: array u8 16sz -> u128 = magic ()
let to_le_bytes_under_impl_10: u128 -> array u8 16sz = magic ()
let to_be_bytes_under_impl_10: u128 -> array u8 16sz = magic ()
let rotate_right_under_impl_10: u128 -> u128 -> u128 = magic ()


