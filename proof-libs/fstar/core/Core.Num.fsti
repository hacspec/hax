module Core.Num
open Rust_primitives

let impl__u8__wrapping_sub: u8 -> u8 -> u8 = sub_mod
let impl__u16__wrapping_add: u16 -> u16 ->  u16 = add_mod
let impl__i32__wrapping_add: i32 -> i32 -> i32 = add_mod
val impl__i32__abs: i32 -> i32
val impl__i32__pow: i32 -> u32 -> i32

let impl__u32__wrapping_add: u32 -> u32 -> u32 = add_mod
val impl__u32__rotate_left: u32 -> u32 -> u32
val impl__u32__from_le_bytes: t_Array u8 (sz 4) -> u32
val impl__u32__from_be_bytes: t_Array u8 (sz 4) -> u32
val impl__u32__to_le_bytes: u32 -> t_Array u8 (sz 4)
val impl__u32__to_be_bytes: u32 -> t_Array u8 (sz 4)
val impl__u32__rotate_right: u32 -> u32 -> u32

let impl__u64__wrapping_add: u64 -> u64 -> u64 = add_mod
val impl__u64__rotate_left: u32 -> u32 -> u32
val impl__u64__from_le_bytes: t_Array u8 (sz 8) -> u64
val impl__u64__from_be_bytes: t_Array u8 (sz 8) -> u64
val impl__u64__to_le_bytes: u64 -> t_Array u8 (sz 8)
val impl__u64__to_be_bytes: u64 -> t_Array u8 (sz 8)
val impl__u64__rotate_right: u64 -> u64 -> u64

let impl__u128__wrapping_add (x: u128) (y: u128): u128 = FStar.UInt128.add_underspec x y
val impl__u128__rotate_left: u128 -> u128 -> u128
val impl__u128__from_le_bytes: t_Array u8 (sz 16) -> u128
val impl__u128__from_be_bytes: t_Array u8 (sz 16) -> u128
val impl__u128__to_le_bytes: u128 -> t_Array u8 (sz 16)
val impl__u128__to_be_bytes: u128 -> t_Array u8 (sz 16)
val impl__u128__rotate_right: u128 -> u128 -> u128

val impl__u8__pow: u8 -> u32 -> u8
val impl__u16__pow (base: u16) (exponent: u32): result : u16 {v base == 2 /\ v exponent < 16 ==> result == mk_int #Lib.IntTypes.U16 (pow2 (v exponent))}
val impl__u32__pow (base: u32) (exponent: u32): result : u32 {v base == 2 /\ v exponent <= 16 ==> result == mk_int #Lib.IntTypes.U32 (pow2 (v exponent))}
val impl__u64__pow: u64 -> u32 -> u64
val impl__u128__pow: u128 -> u32 -> u128
val impl__i32__pow (base: i32) (exponent: u32): result: i32 {v base == 2 /\ v exponent <= 16 ==> result == mk_int #Lib.IntTypes.S32 (pow2 (v exponent))}

val impl__u8__from_str_radix: string -> u32 -> Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError

val impl__usize__ilog2: i32 -> u32 


