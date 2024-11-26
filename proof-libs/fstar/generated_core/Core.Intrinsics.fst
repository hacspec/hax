module Core.Intrinsics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_i128 as add_with_overflow_i128}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_i16 as add_with_overflow_i16}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_i32 as add_with_overflow_i32}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_i64 as add_with_overflow_i64}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_i8 as add_with_overflow_i8}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_isize as add_with_overflow_isize}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_i128 as unchecked_add_i128}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_i16 as unchecked_add_i16}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_i32 as unchecked_add_i32}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_i64 as unchecked_add_i64}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_i8 as unchecked_add_i8}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_isize as unchecked_add_isize}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_u128 as unchecked_add_u128}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_u16 as unchecked_add_u16}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_u32 as unchecked_add_u32}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_u64 as unchecked_add_u64}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_u8 as unchecked_add_u8}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_add_usize as unchecked_add_usize}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_u128 as add_with_overflow_u128}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_u16 as add_with_overflow_u16}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_u32 as add_with_overflow_u32}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_u64 as add_with_overflow_u64}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_u8 as add_with_overflow_u8}

include Core.Intrinsics.Rec_bundle_253787241 {add_with_overflow_usize as add_with_overflow_usize}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_u128 as unchecked_div_u128}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_u16 as unchecked_div_u16}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_u32 as unchecked_div_u32}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_u64 as unchecked_div_u64}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_u8 as unchecked_div_u8}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_usize as unchecked_div_usize}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_i128 as wrapping_add_i128}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_i16 as wrapping_add_i16}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_i32 as wrapping_add_i32}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_i64 as wrapping_add_i64}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_i8 as wrapping_add_i8}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_isize as wrapping_add_isize}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_i128 as wrapping_sub_i128}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_i16 as wrapping_sub_i16}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_i32 as wrapping_sub_i32}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_i64 as wrapping_sub_i64}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_i8 as wrapping_sub_i8}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_isize as wrapping_sub_isize}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_i128 as unchecked_div_i128}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_i16 as unchecked_div_i16}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_i32 as unchecked_div_i32}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_i64 as unchecked_div_i64}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_i8 as unchecked_div_i8}

include Core.Intrinsics.Rec_bundle_253787241 {unchecked_div_isize as unchecked_div_isize}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_u128 as wrapping_add_u128}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_u16 as wrapping_add_u16}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_u32 as wrapping_add_u32}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_u64 as wrapping_add_u64}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_u8 as wrapping_add_u8}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_add_usize as wrapping_add_usize}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_i128 as wrapping_mul_i128}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_i16 as wrapping_mul_i16}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_i32 as wrapping_mul_i32}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_i64 as wrapping_mul_i64}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_i8 as wrapping_mul_i8}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_isize as wrapping_mul_isize}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_u128 as wrapping_mul_u128}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_u16 as wrapping_mul_u16}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_u32 as wrapping_mul_u32}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_u64 as wrapping_mul_u64}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_u8 as wrapping_mul_u8}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_mul_usize as wrapping_mul_usize}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_u128 as wrapping_sub_u128}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_u16 as wrapping_sub_u16}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_u32 as wrapping_sub_u32}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_u64 as wrapping_sub_u64}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_u8 as wrapping_sub_u8}

include Core.Intrinsics.Rec_bundle_253787241 {wrapping_sub_usize as wrapping_sub_usize}

include Core.Intrinsics.Rec_bundle_253787241 {bswap_u8 as bswap_u8}

include Core.Intrinsics.Rec_bundle_253787241 {ctpop_u8 as ctpop_u8}

include Core.Intrinsics.Rec_bundle_253787241 {cttz_u8 as cttz_u8}

include Core.Intrinsics.Rec_bundle_253787241 {bswap_u16 as bswap_u16}

include Core.Intrinsics.Rec_bundle_253787241 {ctpop_u16 as ctpop_u16}

include Core.Intrinsics.Rec_bundle_253787241 {cttz_u16 as cttz_u16}

include Core.Intrinsics.Rec_bundle_253787241 {bswap_u32 as bswap_u32}

include Core.Intrinsics.Rec_bundle_253787241 {ctpop_u32 as ctpop_u32}

include Core.Intrinsics.Rec_bundle_253787241 {cttz_u32 as cttz_u32}

include Core.Intrinsics.Rec_bundle_253787241 {bswap_u64 as bswap_u64}

include Core.Intrinsics.Rec_bundle_253787241 {ctpop_u64 as ctpop_u64}

include Core.Intrinsics.Rec_bundle_253787241 {cttz_u64 as cttz_u64}

include Core.Intrinsics.Rec_bundle_253787241 {bswap_u128 as bswap_u128}

include Core.Intrinsics.Rec_bundle_253787241 {ctpop_u128 as ctpop_u128}

include Core.Intrinsics.Rec_bundle_253787241 {cttz_u128 as cttz_u128}

include Core.Intrinsics.Rec_bundle_253787241 {bswap_usize as bswap_usize}

include Core.Intrinsics.Rec_bundle_253787241 {ctpop_usize as ctpop_usize}

include Core.Intrinsics.Rec_bundle_253787241 {cttz_usize as cttz_usize}

include Core.Intrinsics.Rec_bundle_253787241 {ctlz_u128 as ctlz_u128}

include Core.Intrinsics.Rec_bundle_253787241 {ctlz_u16 as ctlz_u16}

include Core.Intrinsics.Rec_bundle_253787241 {ctlz_u32 as ctlz_u32}

include Core.Intrinsics.Rec_bundle_253787241 {ctlz_u64 as ctlz_u64}

include Core.Intrinsics.Rec_bundle_253787241 {ctlz_u8 as ctlz_u8}

include Core.Intrinsics.Rec_bundle_253787241 {ctlz_usize as ctlz_usize}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_left_u128 as rotate_left_u128}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_left_u16 as rotate_left_u16}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_left_u32 as rotate_left_u32}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_left_u64 as rotate_left_u64}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_left_u8 as rotate_left_u8}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_left_usize as rotate_left_usize}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_right_u128 as rotate_right_u128}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_right_u16 as rotate_right_u16}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_right_u32 as rotate_right_u32}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_right_u64 as rotate_right_u64}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_right_u8 as rotate_right_u8}

include Core.Intrinsics.Rec_bundle_253787241 {rotate_right_usize as rotate_right_usize}
