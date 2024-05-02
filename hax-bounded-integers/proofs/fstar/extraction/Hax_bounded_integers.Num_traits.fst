module Hax_bounded_integers.Num_traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_BitOps (v_Self: Type) = {
  f_Output:Type;
  f_count_ones_pre:v_Self -> bool;
  f_count_ones_post:v_Self -> u32 -> bool;
  f_count_ones:x0: v_Self
    -> Prims.Pure u32 (f_count_ones_pre x0) (fun result -> f_count_ones_post x0 result);
  f_count_zeros_pre:v_Self -> bool;
  f_count_zeros_post:v_Self -> u32 -> bool;
  f_count_zeros:x0: v_Self
    -> Prims.Pure u32 (f_count_zeros_pre x0) (fun result -> f_count_zeros_post x0 result);
  f_leading_ones_pre:v_Self -> bool;
  f_leading_ones_post:v_Self -> u32 -> bool;
  f_leading_ones:x0: v_Self
    -> Prims.Pure u32 (f_leading_ones_pre x0) (fun result -> f_leading_ones_post x0 result);
  f_leading_zeros_pre:v_Self -> bool;
  f_leading_zeros_post:v_Self -> u32 -> bool;
  f_leading_zeros:x0: v_Self
    -> Prims.Pure u32 (f_leading_zeros_pre x0) (fun result -> f_leading_zeros_post x0 result);
  f_trailing_ones_pre:v_Self -> bool;
  f_trailing_ones_post:v_Self -> u32 -> bool;
  f_trailing_ones:x0: v_Self
    -> Prims.Pure u32 (f_trailing_ones_pre x0) (fun result -> f_trailing_ones_post x0 result);
  f_trailing_zeros_pre:v_Self -> bool;
  f_trailing_zeros_post:v_Self -> u32 -> bool;
  f_trailing_zeros:x0: v_Self
    -> Prims.Pure u32 (f_trailing_zeros_pre x0) (fun result -> f_trailing_zeros_post x0 result);
  f_rotate_left_pre:v_Self -> u32 -> bool;
  f_rotate_left_post:v_Self -> u32 -> f_Output -> bool;
  f_rotate_left:x0: v_Self -> x1: u32
    -> Prims.Pure f_Output (f_rotate_left_pre x0 x1) (fun result -> f_rotate_left_post x0 x1 result);
  f_rotate_right_pre:v_Self -> u32 -> bool;
  f_rotate_right_post:v_Self -> u32 -> f_Output -> bool;
  f_rotate_right:x0: v_Self -> x1: u32
    -> Prims.Pure f_Output
        (f_rotate_right_pre x0 x1)
        (fun result -> f_rotate_right_post x0 x1 result);
  f_from_be_pre:v_Self -> bool;
  f_from_be_post:v_Self -> f_Output -> bool;
  f_from_be:x0: v_Self
    -> Prims.Pure f_Output (f_from_be_pre x0) (fun result -> f_from_be_post x0 result);
  f_from_le_pre:v_Self -> bool;
  f_from_le_post:v_Self -> f_Output -> bool;
  f_from_le:x0: v_Self
    -> Prims.Pure f_Output (f_from_le_pre x0) (fun result -> f_from_le_post x0 result);
  f_to_be_pre:v_Self -> bool;
  f_to_be_post:v_Self -> f_Output -> bool;
  f_to_be:x0: v_Self -> Prims.Pure f_Output (f_to_be_pre x0) (fun result -> f_to_be_post x0 result);
  f_to_le_pre:v_Self -> bool;
  f_to_le_post:v_Self -> f_Output -> bool;
  f_to_le:x0: v_Self -> Prims.Pure f_Output (f_to_le_pre x0) (fun result -> f_to_le_post x0 result);
  f_pow_pre:v_Self -> u32 -> bool;
  f_pow_post:v_Self -> u32 -> f_Output -> bool;
  f_pow:x0: v_Self -> x1: u32
    -> Prims.Pure f_Output (f_pow_pre x0 x1) (fun result -> f_pow_post x0 x1 result)
}

class t_Bounded (v_Self: Type) = {
  f_min_value_pre:Prims.unit -> bool;
  f_min_value_post:Prims.unit -> v_Self -> bool;
  f_min_value:x0: Prims.unit
    -> Prims.Pure v_Self (f_min_value_pre x0) (fun result -> f_min_value_post x0 result);
  f_max_value_pre:Prims.unit -> bool;
  f_max_value_post:Prims.unit -> v_Self -> bool;
  f_max_value:x0: Prims.unit
    -> Prims.Pure v_Self (f_max_value_pre x0) (fun result -> f_max_value_post x0 result)
}

class t_CheckedAdd (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_checked_add_pre:v_Self -> v_Rhs -> bool;
  f_checked_add_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_add:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_add_pre x0 x1)
        (fun result -> f_checked_add_post x0 x1 result)
}

class t_CheckedDiv (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_checked_div_pre:v_Self -> v_Rhs -> bool;
  f_checked_div_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_div:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_div_pre x0 x1)
        (fun result -> f_checked_div_post x0 x1 result)
}

class t_CheckedMul (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_checked_mul_pre:v_Self -> v_Rhs -> bool;
  f_checked_mul_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_mul:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_mul_pre x0 x1)
        (fun result -> f_checked_mul_post x0 x1 result)
}

class t_CheckedNeg (v_Self: Type) = {
  f_Output:Type;
  f_checked_neg_pre:v_Self -> bool;
  f_checked_neg_post:v_Self -> Core.Option.t_Option f_Output -> bool;
  f_checked_neg:x0: v_Self
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_neg_pre x0)
        (fun result -> f_checked_neg_post x0 result)
}

class t_CheckedSub (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_checked_sub_pre:v_Self -> v_Rhs -> bool;
  f_checked_sub_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_sub:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_sub_pre x0 x1)
        (fun result -> f_checked_sub_post x0 x1 result)
}

class t_FromBytes (v_Self: Type) = {
  f_BYTES:Type;
  f_from_le_bytes_pre:f_BYTES -> bool;
  f_from_le_bytes_post:f_BYTES -> v_Self -> bool;
  f_from_le_bytes:x0: f_BYTES
    -> Prims.Pure v_Self (f_from_le_bytes_pre x0) (fun result -> f_from_le_bytes_post x0 result);
  f_from_be_bytes_pre:f_BYTES -> bool;
  f_from_be_bytes_post:f_BYTES -> v_Self -> bool;
  f_from_be_bytes:x0: f_BYTES
    -> Prims.Pure v_Self (f_from_be_bytes_pre x0) (fun result -> f_from_be_bytes_post x0 result)
}

class t_NumOps (v_Self: Type) (v_Rhs: Type) (v_Output: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_3420555054487092457:Core.Ops.Arith.t_Add v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_16858356355397389837:Core.Ops.Arith.t_Sub v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_3009625865770964073:Core.Ops.Arith.t_Mul v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9111207129981210576:Core.Ops.Arith.t_Div v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_16804214316696687705:Core.Ops.Arith.t_Rem v_Self
    v_Rhs
}

class t_One (v_Self: Type) = {
  f_one_pre:Prims.unit -> bool;
  f_one_post:Prims.unit -> v_Self -> bool;
  f_one:x0: Prims.unit -> Prims.Pure v_Self (f_one_pre x0) (fun result -> f_one_post x0 result)
}

class t_ToBytes (v_Self: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_4530633244223603628:t_FromBytes v_Self;
  f_to_le_bytes_pre:v_Self -> bool;
  f_to_le_bytes_post:v_Self -> v_4530633244223603628.f_BYTES -> bool;
  f_to_le_bytes:x0: v_Self
    -> Prims.Pure v_4530633244223603628.f_BYTES
        (f_to_le_bytes_pre x0)
        (fun result -> f_to_le_bytes_post x0 result);
  f_to_be_bytes_pre:v_Self -> bool;
  f_to_be_bytes_post:v_Self -> v_4530633244223603628.f_BYTES -> bool;
  f_to_be_bytes:x0: v_Self
    -> Prims.Pure v_4530633244223603628.f_BYTES
        (f_to_be_bytes_pre x0)
        (fun result -> f_to_be_bytes_post x0 result)
}

class t_WrappingAdd (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_wrapping_add_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_add_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_add:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_add_pre x0 x1)
        (fun result -> f_wrapping_add_post x0 x1 result)
}

class t_WrappingDiv (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_wrapping_div_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_div_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_div:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_div_pre x0 x1)
        (fun result -> f_wrapping_div_post x0 x1 result)
}

class t_WrappingMul (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_wrapping_mul_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_mul_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_mul:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_mul_pre x0 x1)
        (fun result -> f_wrapping_mul_post x0 x1 result)
}

class t_WrappingSub (v_Self: Type) (v_Rhs: Type) = {
  f_Output:Type;
  f_wrapping_sub_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_sub_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_sub:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_sub_pre x0 x1)
        (fun result -> f_wrapping_sub_post x0 x1 result)
}

class t_Zero (v_Self: Type) = {
  f_zero_pre:Prims.unit -> bool;
  f_zero_post:Prims.unit -> v_Self -> bool;
  f_zero:x0: Prims.unit -> Prims.Pure v_Self (f_zero_pre x0) (fun result -> f_zero_post x0 result)
}

class t_MachineInt (v_Self: Type) (v_Output: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_957087622381469234:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_7243498280507755391:t_Bounded v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9802961870013064174:Core.Cmp.t_PartialOrd v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15372362079243870652:Core.Cmp.t_Ord v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1959006841676202949:Core.Cmp.t_PartialEq v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_8995075768394296398:Core.Cmp.t_Eq v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_2630392019625310516:t_Zero v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_6913784476497246329:t_One v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9936546819275964215:Core.Ops.Bit.t_Not v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1531387235085686842:t_NumOps v_Self
    v_Self
    v_Output;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_3786882699227749486:Core.Ops.Bit.t_BitAnd v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_8095144530696857283:Core.Ops.Bit.t_BitOr v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15313863003467220491:Core.Ops.Bit.t_BitXor v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13306778606414288955:Core.Ops.Bit.t_Shl v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_2333720355461387358:Core.Ops.Bit.t_Shr v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_10133521522977299931:t_CheckedAdd v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_16509367665728242671:t_CheckedSub v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_261087305577220356:t_CheckedMul v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_4808020806666262858:t_CheckedDiv v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_18005178388944789845:t_WrappingAdd v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11471591230230619611:t_WrappingSub v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_5940229659009370734:t_WrappingMul v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1640938766960073185:t_WrappingDiv v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12477248635475532096:t_BitOps v_Self
}
