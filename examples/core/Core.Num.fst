module Core.Num
open Core.Types
open FStar.Integers
open FStar.UInt32

let impl_8__wrapping_add (x: u32) (y: u32): u32 = add_underspec x y
let impl_8__rotate_left x y = x
let impl_8__from_le_bytes: array u8 4sz -> u32 = magic ()
let impl_8__from_be_bytes: array u8 4sz -> u32 = magic ()
let impl_8__to_le_bytes: u32 -> array u8 4sz = magic ()
let impl_8__to_be_bytes: u32 -> array u8 4sz = magic ()
let impl_8__rotate_right: u32 -> u32 -> u32 = magic ()


open FStar.UInt64
let impl_9__wrapping_add (x: u64) (y: u64): u64 = add_underspec x y
let impl_9__rotate_left x y = x
let impl_9__from_le_bytes: array u8 8sz -> u64 = magic ()
let impl_9__from_be_bytes: array u8 8sz -> u64 = magic ()
let impl_9__to_le_bytes: u64 -> array u8 8sz = magic ()
let impl_9__to_be_bytes: u64 -> array u8 8sz = magic ()
let impl_9__rotate_right: u64 -> u64 -> u64 = magic ()


open FStar.UInt128
let impl_10__wrapping_add (x: u128) (y: u128): u128 = add_underspec x y
let impl_10__rotate_left x y = x
let impl_10__from_le_bytes: array u8 16sz -> u128 = magic ()
let impl_10__from_be_bytes: array u8 16sz -> u128 = magic ()
let impl_10__to_le_bytes: u128 -> array u8 16sz = magic ()
let impl_10__to_be_bytes: u128 -> array u8 16sz = magic ()
let impl_10__rotate_right: u128 -> u128 -> u128 = magic ()

let impl_6__pow: u8 -> u8 -> u8 = magic ()


