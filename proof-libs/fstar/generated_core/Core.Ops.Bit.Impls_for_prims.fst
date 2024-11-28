module Core.Ops.Bit.Impls_for_prims
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_84: Core.Ops.Bit.t_BitOr Core.Primitive.t_i8 Core.Primitive.t_i8 =
  {
    f_Output = Core.Primitive.t_i8;
    f_bitor_pre = (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) (out: Core.Primitive.t_i8) -> true
    );
    f_bitor
    =
    fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) ->
      Core.Primitive.C_i8 (self.Core.Primitive._0 |. other.Core.Primitive._0) <: Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_85: Core.Ops.Bit.t_BitOr Core.Primitive.t_i16 Core.Primitive.t_i16 =
  {
    f_Output = Core.Primitive.t_i16;
    f_bitor_pre = (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) (out: Core.Primitive.t_i16) ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) ->
      Core.Primitive.C_i16 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_86: Core.Ops.Bit.t_BitOr Core.Primitive.t_i32 Core.Primitive.t_i32 =
  {
    f_Output = Core.Primitive.t_i32;
    f_bitor_pre = (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) (out: Core.Primitive.t_i32) ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) ->
      Core.Primitive.C_i32 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_87: Core.Ops.Bit.t_BitOr Core.Primitive.t_i64 Core.Primitive.t_i64 =
  {
    f_Output = Core.Primitive.t_i64;
    f_bitor_pre = (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) (out: Core.Primitive.t_i64) ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) ->
      Core.Primitive.C_i64 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_88: Core.Ops.Bit.t_BitOr Core.Primitive.t_i128 Core.Primitive.t_i128 =
  {
    f_Output = Core.Primitive.t_i128;
    f_bitor_pre = (fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) -> true);
    f_bitor_post
    =
    (fun
        (self: Core.Primitive.t_i128)
        (other: Core.Primitive.t_i128)
        (out: Core.Primitive.t_i128)
        ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) ->
      Core.Primitive.C_i128 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_89: Core.Ops.Bit.t_BitOr Core.Primitive.t_isize Core.Primitive.t_isize =
  {
    f_Output = Core.Primitive.t_isize;
    f_bitor_pre = (fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) -> true);
    f_bitor_post
    =
    (fun
        (self: Core.Primitive.t_isize)
        (other: Core.Primitive.t_isize)
        (out: Core.Primitive.t_isize)
        ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) ->
      Core.Primitive.C_isize (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Ops.Bit.t_Shr Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shr_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_shr
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Ops.Bit.t_Shr Core.Primitive.t_u8 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shr_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u16) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u8) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Bit.t_Shr Core.Primitive.t_u8 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shr_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u32) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u8) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Ops.Bit.t_Shr Core.Primitive.t_u8 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shr_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u64) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u8) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Ops.Bit.t_Shr Core.Primitive.t_u8 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shr_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u128) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u8) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Ops.Bit.t_Shr Core.Primitive.t_u8 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u8;
    f_shr_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_usize) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u8) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Ops.Bit.t_Shr Core.Primitive.t_u16 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shr_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u8) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u16) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Ops.Bit.t_Shr Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shr_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Ops.Bit.t_Shr Core.Primitive.t_u16 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shr_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u32) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u16) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Ops.Bit.t_Shr Core.Primitive.t_u16 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shr_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u64) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u16) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Ops.Bit.t_Shr Core.Primitive.t_u16 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shr_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u128) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u16) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Ops.Bit.t_Shr Core.Primitive.t_u16 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u16;
    f_shr_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_usize) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u16) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Ops.Bit.t_Shr Core.Primitive.t_u32 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shr_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u8) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u32) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Ops.Bit.t_Shr Core.Primitive.t_u32 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shr_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u16) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u32) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Ops.Bit.t_Shr Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shr_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Ops.Bit.t_Shr Core.Primitive.t_u32 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shr_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u64) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u32) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Ops.Bit.t_Shr Core.Primitive.t_u32 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shr_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u128) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u32) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Ops.Bit.t_Shr Core.Primitive.t_u32 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u32;
    f_shr_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_usize) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u32) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Ops.Bit.t_Shr Core.Primitive.t_u64 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shr_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u8) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u64) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Ops.Bit.t_Shr Core.Primitive.t_u64 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shr_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u16) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u64) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Ops.Bit.t_Shr Core.Primitive.t_u64 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shr_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u32) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u64) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Ops.Bit.t_Shr Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shr_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Ops.Bit.t_Shr Core.Primitive.t_u64 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shr_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u128) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u64) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Ops.Bit.t_Shr Core.Primitive.t_u64 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u64;
    f_shr_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_usize) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u64) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Ops.Bit.t_Shr Core.Primitive.t_u128 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shr_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u8) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u128) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Ops.Bit.t_Shr Core.Primitive.t_u128 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shr_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u16) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u128) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Ops.Bit.t_Shr Core.Primitive.t_u128 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shr_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u32) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u128) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Ops.Bit.t_Shr Core.Primitive.t_u128 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shr_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u64) -> true);
    f_shr_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u128) ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Ops.Bit.t_Shr Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shr_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Ops.Bit.t_Shr Core.Primitive.t_u128 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u128;
    f_shr_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_usize) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Ops.Bit.t_Shr Core.Primitive.t_usize Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shr_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u8) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u8)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Ops.Bit.t_Shr Core.Primitive.t_usize Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shr_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u16) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u16)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Ops.Bit.t_Shr Core.Primitive.t_usize Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shr_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u32) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u32)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Ops.Bit.t_Shr Core.Primitive.t_usize Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shr_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u64) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u64)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Ops.Bit.t_Shr Core.Primitive.t_usize Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shr_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u128) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Ops.Bit.t_Shr Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_shr_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_shr_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shr
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 >>! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Ops.Bit.t_Shl Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shl_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_shl
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Ops.Bit.t_Shl Core.Primitive.t_u8 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shl_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u16) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u8) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Ops.Bit.t_Shl Core.Primitive.t_u8 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shl_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u32) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u8) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Ops.Bit.t_Shl Core.Primitive.t_u8 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shl_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u64) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u8) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Ops.Bit.t_Shl Core.Primitive.t_u8 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u8;
    f_shl_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u128) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u8) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: Core.Ops.Bit.t_Shl Core.Primitive.t_u8 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u8;
    f_shl_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_usize) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u8) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: Core.Ops.Bit.t_Shl Core.Primitive.t_u16 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shl_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u8) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u16) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Ops.Bit.t_Shl Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shl_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Ops.Bit.t_Shl Core.Primitive.t_u16 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shl_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u32) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u16) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Ops.Bit.t_Shl Core.Primitive.t_u16 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shl_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u64) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u16) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Ops.Bit.t_Shl Core.Primitive.t_u16 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u16;
    f_shl_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u128) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u16) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: Core.Ops.Bit.t_Shl Core.Primitive.t_u16 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u16;
    f_shl_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_usize) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u16) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: Core.Ops.Bit.t_Shl Core.Primitive.t_u32 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shl_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u8) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u32) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: Core.Ops.Bit.t_Shl Core.Primitive.t_u32 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shl_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u16) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u32) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: Core.Ops.Bit.t_Shl Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shl_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: Core.Ops.Bit.t_Shl Core.Primitive.t_u32 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shl_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u64) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u32) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: Core.Ops.Bit.t_Shl Core.Primitive.t_u32 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u32;
    f_shl_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u128) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u32) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: Core.Ops.Bit.t_Shl Core.Primitive.t_u32 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u32;
    f_shl_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_usize) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u32) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: Core.Ops.Bit.t_Shl Core.Primitive.t_u64 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shl_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u8) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u64) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: Core.Ops.Bit.t_Shl Core.Primitive.t_u64 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shl_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u16) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u64) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: Core.Ops.Bit.t_Shl Core.Primitive.t_u64 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shl_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u32) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u64) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: Core.Ops.Bit.t_Shl Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shl_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: Core.Ops.Bit.t_Shl Core.Primitive.t_u64 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u64;
    f_shl_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u128) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u128) (out: Core.Primitive.t_u64) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: Core.Ops.Bit.t_Shl Core.Primitive.t_u64 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u64;
    f_shl_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_usize) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_usize) (out: Core.Primitive.t_u64) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_66: Core.Ops.Bit.t_Shl Core.Primitive.t_u128 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shl_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u8) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u128) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_67: Core.Ops.Bit.t_Shl Core.Primitive.t_u128 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shl_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u16) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u128) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_68: Core.Ops.Bit.t_Shl Core.Primitive.t_u128 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shl_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u32) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u128) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_69: Core.Ops.Bit.t_Shl Core.Primitive.t_u128 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shl_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u64) -> true);
    f_shl_post
    =
    (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u128) ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_70: Core.Ops.Bit.t_Shl Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_shl_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_71: Core.Ops.Bit.t_Shl Core.Primitive.t_u128 Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_u128;
    f_shl_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_usize) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_72: Core.Ops.Bit.t_Shl Core.Primitive.t_usize Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shl_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u8) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u8)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_73: Core.Ops.Bit.t_Shl Core.Primitive.t_usize Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shl_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u16) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u16)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_74: Core.Ops.Bit.t_Shl Core.Primitive.t_usize Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shl_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u32) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u32)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_75: Core.Ops.Bit.t_Shl Core.Primitive.t_usize Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shl_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u64) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u64)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_76: Core.Ops.Bit.t_Shl Core.Primitive.t_usize Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_usize;
    f_shl_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u128) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_77: Core.Ops.Bit.t_Shl Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_shl_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_shl_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_shl
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 <<! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_78: Core.Ops.Bit.t_BitOr Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_bitor_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_bitor
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 |. other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_79: Core.Ops.Bit.t_BitOr Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_bitor_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_80: Core.Ops.Bit.t_BitOr Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_bitor_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_81: Core.Ops.Bit.t_BitOr Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_bitor_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_bitor_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_82: Core.Ops.Bit.t_BitOr Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_bitor_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_bitor_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_83: Core.Ops.Bit.t_BitOr Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_bitor_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_bitor_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_bitor
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 |. other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_90: Core.Ops.Bit.t_BitXor Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_bitxor_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_bitxor_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_bitxor
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 ^. other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_91: Core.Ops.Bit.t_BitXor Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_bitxor_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_bitxor_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_bitxor
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 ^. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_92: Core.Ops.Bit.t_BitXor Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_bitxor_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_bitxor_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_bitxor
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 ^. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_93: Core.Ops.Bit.t_BitXor Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_bitxor_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_bitxor_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_bitxor
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 ^. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_94: Core.Ops.Bit.t_BitXor Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_bitxor_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_bitxor_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_bitxor
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 ^. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_95: Core.Ops.Bit.t_BitXor Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_bitxor_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_bitxor_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_bitxor
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 ^. other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_96: Core.Ops.Bit.t_BitAnd Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_bitand_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_bitand_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_bitand
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 &. other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_97: Core.Ops.Bit.t_BitAnd Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_bitand_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_bitand_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_bitand
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 &. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_98: Core.Ops.Bit.t_BitAnd Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_bitand_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_bitand_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_bitand
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 &. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_99: Core.Ops.Bit.t_BitAnd Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_bitand_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_bitand_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_bitand
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 &. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_100: Core.Ops.Bit.t_BitAnd Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_bitand_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_bitand_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_bitand
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 &. other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_101: Core.Ops.Bit.t_BitAnd Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_bitand_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_bitand_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_bitand
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 &. other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Bit.t_Not Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_not_pre = (fun (self: Core.Primitive.t_u8) -> true);
    f_not_post = (fun (self: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true);
    f_not
    =
    fun (self: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 ~.self.Core.Primitive._0 <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Bit.t_Not Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_not_pre = (fun (self: Core.Primitive.t_u16) -> true);
    f_not_post = (fun (self: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) -> true);
    f_not
    =
    fun (self: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 ~.self.Core.Primitive._0 <: Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Ops.Bit.t_Not Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_not_pre = (fun (self: Core.Primitive.t_u32) -> true);
    f_not_post = (fun (self: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) -> true);
    f_not
    =
    fun (self: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 ~.self.Core.Primitive._0 <: Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Bit.t_Not Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_not_pre = (fun (self: Core.Primitive.t_u64) -> true);
    f_not_post = (fun (self: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) -> true);
    f_not
    =
    fun (self: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 ~.self.Core.Primitive._0 <: Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Ops.Bit.t_Not Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_not_pre = (fun (self: Core.Primitive.t_u128) -> true);
    f_not_post = (fun (self: Core.Primitive.t_u128) (out: Core.Primitive.t_u128) -> true);
    f_not
    =
    fun (self: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 ~.self.Core.Primitive._0 <: Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Ops.Bit.t_Not Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_not_pre = (fun (self: Core.Primitive.t_usize) -> true);
    f_not_post = (fun (self: Core.Primitive.t_usize) (out: Core.Primitive.t_usize) -> true);
    f_not
    =
    fun (self: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize ~.self.Core.Primitive._0 <: Core.Primitive.t_usize
  }
