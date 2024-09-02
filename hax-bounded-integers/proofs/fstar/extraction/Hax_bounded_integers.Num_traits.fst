module Hax_bounded_integers.Num_traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_BitOps (v_Self: Type0) = {
  f_Output:Type0;
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

class t_CheckedAdd (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_checked_add_pre:v_Self -> v_Rhs -> bool;
  f_checked_add_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_add:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_add_pre x0 x1)
        (fun result -> f_checked_add_post x0 x1 result)
}

class t_CheckedDiv (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_checked_div_pre:v_Self -> v_Rhs -> bool;
  f_checked_div_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_div:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_div_pre x0 x1)
        (fun result -> f_checked_div_post x0 x1 result)
}

class t_CheckedMul (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_checked_mul_pre:v_Self -> v_Rhs -> bool;
  f_checked_mul_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_mul:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_mul_pre x0 x1)
        (fun result -> f_checked_mul_post x0 x1 result)
}

class t_CheckedNeg (v_Self: Type0) = {
  f_Output:Type0;
  f_checked_neg_pre:v_Self -> bool;
  f_checked_neg_post:v_Self -> Core.Option.t_Option f_Output -> bool;
  f_checked_neg:x0: v_Self
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_neg_pre x0)
        (fun result -> f_checked_neg_post x0 result)
}

class t_CheckedSub (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_checked_sub_pre:v_Self -> v_Rhs -> bool;
  f_checked_sub_post:v_Self -> v_Rhs -> Core.Option.t_Option f_Output -> bool;
  f_checked_sub:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option f_Output)
        (f_checked_sub_pre x0 x1)
        (fun result -> f_checked_sub_post x0 x1 result)
}

class t_FromBytes (v_Self: Type0) = {
  f_BYTES:Type0;
  f_from_le_bytes_pre:f_BYTES -> bool;
  f_from_le_bytes_post:f_BYTES -> v_Self -> bool;
  f_from_le_bytes:x0: f_BYTES
    -> Prims.Pure v_Self (f_from_le_bytes_pre x0) (fun result -> f_from_le_bytes_post x0 result);
  f_from_be_bytes_pre:f_BYTES -> bool;
  f_from_be_bytes_post:f_BYTES -> v_Self -> bool;
  f_from_be_bytes:x0: f_BYTES
    -> Prims.Pure v_Self (f_from_be_bytes_pre x0) (fun result -> f_from_be_bytes_post x0 result)
}

class t_NumOps (v_Self: Type0) (v_Rhs: Type0) (v_Output: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9126539072073536218:Core.Ops.Arith.t_Add v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9784678892199232396:Core.Ops.Arith.t_Sub v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_7005199110250618039:Core.Ops.Arith.t_Mul v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12366019628759357413:Core.Ops.Arith.t_Div v_Self
    v_Rhs;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11859756759858186302:Core.Ops.Arith.t_Rem v_Self
    v_Rhs
}

class t_One (v_Self: Type0) = {
  f_one_pre:Prims.unit -> bool;
  f_one_post:Prims.unit -> v_Self -> bool;
  f_one:x0: Prims.unit -> Prims.Pure v_Self (f_one_pre x0) (fun result -> f_one_post x0 result)
}

class t_ToBytes (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_3732703090464998751:t_FromBytes v_Self;
  f_to_le_bytes_pre:v_Self -> bool;
  f_to_le_bytes_post:v_Self -> v_3732703090464998751.f_BYTES -> bool;
  f_to_le_bytes:x0: v_Self
    -> Prims.Pure v_3732703090464998751.f_BYTES
        (f_to_le_bytes_pre x0)
        (fun result -> f_to_le_bytes_post x0 result);
  f_to_be_bytes_pre:v_Self -> bool;
  f_to_be_bytes_post:v_Self -> v_3732703090464998751.f_BYTES -> bool;
  f_to_be_bytes:x0: v_Self
    -> Prims.Pure v_3732703090464998751.f_BYTES
        (f_to_be_bytes_pre x0)
        (fun result -> f_to_be_bytes_post x0 result)
}

class t_WrappingAdd (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_wrapping_add_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_add_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_add:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_add_pre x0 x1)
        (fun result -> f_wrapping_add_post x0 x1 result)
}

class t_WrappingDiv (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_wrapping_div_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_div_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_div:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_div_pre x0 x1)
        (fun result -> f_wrapping_div_post x0 x1 result)
}

class t_WrappingMul (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_wrapping_mul_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_mul_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_mul:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_mul_pre x0 x1)
        (fun result -> f_wrapping_mul_post x0 x1 result)
}

class t_WrappingSub (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_wrapping_sub_pre:v_Self -> v_Rhs -> bool;
  f_wrapping_sub_post:v_Self -> v_Rhs -> f_Output -> bool;
  f_wrapping_sub:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output
        (f_wrapping_sub_pre x0 x1)
        (fun result -> f_wrapping_sub_post x0 x1 result)
}

class t_Zero (v_Self: Type0) = {
  f_zero_pre:Prims.unit -> bool;
  f_zero_post:Prims.unit -> v_Self -> bool;
  f_zero:x0: Prims.unit -> Prims.Pure v_Self (f_zero_pre x0) (fun result -> f_zero_post x0 result)
}

class t_MachineInt (v_Self: Type0) (v_Output: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12866954522599331834:Core.Cmp.t_PartialOrd v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13035911912416111195:Core.Cmp.t_Ord v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12632649257025169145:Core.Cmp.t_PartialEq v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_8099741844003281729:Core.Cmp.t_Eq v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9841570312332416173:t_Zero v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12668241202577409386:t_One v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9487321769118300762:Core.Ops.Bit.t_Not v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1980884762883925305:t_NumOps v_Self
    v_Self
    v_Output;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_13929479875548649875:Core.Ops.Bit.t_BitAnd v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1708325062211865233:Core.Ops.Bit.t_BitOr v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1501688608269502122:Core.Ops.Bit.t_BitXor v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15083490293093561556:Core.Ops.Bit.t_Shl v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9065931548762825726:Core.Ops.Bit.t_Shr v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_5052970308637232515:t_CheckedAdd v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_739902999637339236:t_CheckedSub v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15323401662629887609:t_CheckedMul v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_8119502507145032897:t_CheckedDiv v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12846047806852469117:t_WrappingAdd v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12408554086330550784:t_WrappingSub v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_8633193508996485932:t_WrappingMul v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_16339457892016115661:t_WrappingDiv v_Self v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12348120774285878195:t_BitOps v_Self
}
