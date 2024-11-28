module Core.Ops.Arith.Impls_for_prims
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Arith.t_Neg Core.Primitive.t_i8 =
  {
    f_Output = Core.Primitive.t_i8;
    f_neg_pre = (fun (self: Core.Primitive.t_i8) -> true);
    f_neg_post = (fun (self: Core.Primitive.t_i8) (out: Core.Primitive.t_i8) -> true);
    f_neg
    =
    fun (self: Core.Primitive.t_i8) ->
      Core.Primitive.C_i8
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive._0)
      <:
      Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Arith.t_Neg Core.Primitive.t_i16 =
  {
    f_Output = Core.Primitive.t_i16;
    f_neg_pre = (fun (self: Core.Primitive.t_i16) -> true);
    f_neg_post = (fun (self: Core.Primitive.t_i16) (out: Core.Primitive.t_i16) -> true);
    f_neg
    =
    fun (self: Core.Primitive.t_i16) ->
      Core.Primitive.C_i16
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Ops.Arith.t_Neg Core.Primitive.t_i32 =
  {
    f_Output = Core.Primitive.t_i32;
    f_neg_pre = (fun (self: Core.Primitive.t_i32) -> true);
    f_neg_post = (fun (self: Core.Primitive.t_i32) (out: Core.Primitive.t_i32) -> true);
    f_neg
    =
    fun (self: Core.Primitive.t_i32) ->
      Core.Primitive.C_i32
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Arith.t_Neg Core.Primitive.t_i64 =
  {
    f_Output = Core.Primitive.t_i64;
    f_neg_pre = (fun (self: Core.Primitive.t_i64) -> true);
    f_neg_post = (fun (self: Core.Primitive.t_i64) (out: Core.Primitive.t_i64) -> true);
    f_neg
    =
    fun (self: Core.Primitive.t_i64) ->
      Core.Primitive.C_i64
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Ops.Arith.t_Neg Core.Primitive.t_i128 =
  {
    f_Output = Core.Primitive.t_i128;
    f_neg_pre = (fun (self: Core.Primitive.t_i128) -> true);
    f_neg_post = (fun (self: Core.Primitive.t_i128) (out: Core.Primitive.t_i128) -> true);
    f_neg
    =
    fun (self: Core.Primitive.t_i128) ->
      Core.Primitive.C_i128
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Ops.Arith.t_Neg Core.Primitive.t_isize =
  {
    f_Output = Core.Primitive.t_isize;
    f_neg_pre = (fun (self: Core.Primitive.t_isize) -> true);
    f_neg_post = (fun (self: Core.Primitive.t_isize) (out: Core.Primitive.t_isize) -> true);
    f_neg
    =
    fun (self: Core.Primitive.t_isize) ->
      Core.Primitive.C_isize
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Ops.Arith.t_Add Core.Primitive.t_i8 Core.Primitive.t_i8 =
  {
    f_Output = Core.Primitive.t_i8;
    f_add_pre = (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) (out: Core.Primitive.t_i8) -> true
    );
    f_add
    =
    fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) ->
      Core.Primitive.C_i8 (self.Core.Primitive._0 +! other.Core.Primitive._0) <: Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Ops.Arith.t_Add Core.Primitive.t_i16 Core.Primitive.t_i16 =
  {
    f_Output = Core.Primitive.t_i16;
    f_add_pre = (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) (out: Core.Primitive.t_i16) ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) ->
      Core.Primitive.C_i16 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Ops.Arith.t_Add Core.Primitive.t_i32 Core.Primitive.t_i32 =
  {
    f_Output = Core.Primitive.t_i32;
    f_add_pre = (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) (out: Core.Primitive.t_i32) ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) ->
      Core.Primitive.C_i32 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Ops.Arith.t_Add Core.Primitive.t_i64 Core.Primitive.t_i64 =
  {
    f_Output = Core.Primitive.t_i64;
    f_add_pre = (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) (out: Core.Primitive.t_i64) ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) ->
      Core.Primitive.C_i64 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Ops.Arith.t_Add Core.Primitive.t_i128 Core.Primitive.t_i128 =
  {
    f_Output = Core.Primitive.t_i128;
    f_add_pre = (fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) -> true);
    f_add_post
    =
    (fun
        (self: Core.Primitive.t_i128)
        (other: Core.Primitive.t_i128)
        (out: Core.Primitive.t_i128)
        ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) ->
      Core.Primitive.C_i128 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Ops.Arith.t_Add Core.Primitive.t_isize Core.Primitive.t_isize =
  {
    f_Output = Core.Primitive.t_isize;
    f_add_pre = (fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) -> true);
    f_add_post
    =
    (fun
        (self: Core.Primitive.t_isize)
        (other: Core.Primitive.t_isize)
        (out: Core.Primitive.t_isize)
        ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) ->
      Core.Primitive.C_isize (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Ops.Arith.t_Sub Core.Primitive.t_i8 Core.Primitive.t_i8 =
  {
    f_Output = Core.Primitive.t_i8;
    f_sub_pre = (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) (out: Core.Primitive.t_i8) -> true
    );
    f_sub
    =
    fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) ->
      Core.Primitive.C_i8 (self.Core.Primitive._0 -! other.Core.Primitive._0) <: Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Ops.Arith.t_Sub Core.Primitive.t_i16 Core.Primitive.t_i16 =
  {
    f_Output = Core.Primitive.t_i16;
    f_sub_pre = (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) (out: Core.Primitive.t_i16) ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) ->
      Core.Primitive.C_i16 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Ops.Arith.t_Sub Core.Primitive.t_i32 Core.Primitive.t_i32 =
  {
    f_Output = Core.Primitive.t_i32;
    f_sub_pre = (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) (out: Core.Primitive.t_i32) ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) ->
      Core.Primitive.C_i32 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Ops.Arith.t_Sub Core.Primitive.t_i64 Core.Primitive.t_i64 =
  {
    f_Output = Core.Primitive.t_i64;
    f_sub_pre = (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) (out: Core.Primitive.t_i64) ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) ->
      Core.Primitive.C_i64 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Ops.Arith.t_Sub Core.Primitive.t_i128 Core.Primitive.t_i128 =
  {
    f_Output = Core.Primitive.t_i128;
    f_sub_pre = (fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) -> true);
    f_sub_post
    =
    (fun
        (self: Core.Primitive.t_i128)
        (other: Core.Primitive.t_i128)
        (out: Core.Primitive.t_i128)
        ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) ->
      Core.Primitive.C_i128 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Ops.Arith.t_Sub Core.Primitive.t_isize Core.Primitive.t_isize =
  {
    f_Output = Core.Primitive.t_isize;
    f_sub_pre = (fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) -> true);
    f_sub_post
    =
    (fun
        (self: Core.Primitive.t_isize)
        (other: Core.Primitive.t_isize)
        (out: Core.Primitive.t_isize)
        ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) ->
      Core.Primitive.C_isize (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Ops.Arith.t_Add Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_add_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_add
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 +! other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Ops.Arith.t_Add Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_add_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Arith.t_Add Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_add_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Ops.Arith.t_Add Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_add_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_add_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Ops.Arith.t_Add Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_add_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_add_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Ops.Arith.t_Add Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_add_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_add_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_add
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 +! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Ops.Arith.t_Mul Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_mul_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_mul
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 *! other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Ops.Arith.t_Mul Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_mul_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Ops.Arith.t_Mul Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_mul_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Ops.Arith.t_Mul Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_mul_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Ops.Arith.t_Mul Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_mul_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_mul_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Ops.Arith.t_Mul Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_mul_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_mul_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Ops.Arith.t_Mul Core.Primitive.t_i8 Core.Primitive.t_i8 =
  {
    f_Output = Core.Primitive.t_i8;
    f_mul_pre = (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) (out: Core.Primitive.t_i8) -> true
    );
    f_mul
    =
    fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) ->
      Core.Primitive.C_i8 (self.Core.Primitive._0 *! other.Core.Primitive._0) <: Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Ops.Arith.t_Mul Core.Primitive.t_i16 Core.Primitive.t_i16 =
  {
    f_Output = Core.Primitive.t_i16;
    f_mul_pre = (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) (out: Core.Primitive.t_i16) ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) ->
      Core.Primitive.C_i16 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Ops.Arith.t_Mul Core.Primitive.t_i32 Core.Primitive.t_i32 =
  {
    f_Output = Core.Primitive.t_i32;
    f_mul_pre = (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) (out: Core.Primitive.t_i32) ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) ->
      Core.Primitive.C_i32 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Ops.Arith.t_Mul Core.Primitive.t_i64 Core.Primitive.t_i64 =
  {
    f_Output = Core.Primitive.t_i64;
    f_mul_pre = (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) -> true);
    f_mul_post
    =
    (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) (out: Core.Primitive.t_i64) ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) ->
      Core.Primitive.C_i64 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Ops.Arith.t_Mul Core.Primitive.t_i128 Core.Primitive.t_i128 =
  {
    f_Output = Core.Primitive.t_i128;
    f_mul_pre = (fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) -> true);
    f_mul_post
    =
    (fun
        (self: Core.Primitive.t_i128)
        (other: Core.Primitive.t_i128)
        (out: Core.Primitive.t_i128)
        ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) ->
      Core.Primitive.C_i128 (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Ops.Arith.t_Mul Core.Primitive.t_isize Core.Primitive.t_isize =
  {
    f_Output = Core.Primitive.t_isize;
    f_mul_pre = (fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) -> true);
    f_mul_post
    =
    (fun
        (self: Core.Primitive.t_isize)
        (other: Core.Primitive.t_isize)
        (out: Core.Primitive.t_isize)
        ->
        true);
    f_mul
    =
    fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) ->
      Core.Primitive.C_isize (self.Core.Primitive._0 *! other.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Ops.Arith.t_Div Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_div_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_div
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 /! other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Ops.Arith.t_Div Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_div_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Ops.Arith.t_Div Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_div_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Ops.Arith.t_Div Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_div_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Ops.Arith.t_Div Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_div_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_div_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: Core.Ops.Arith.t_Div Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_div_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_div_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: Core.Ops.Arith.t_Rem Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_rem_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_rem
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 %! other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: Core.Ops.Arith.t_Rem Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_rem_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: Core.Ops.Arith.t_Rem Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_rem_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: Core.Ops.Arith.t_Rem Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_rem_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: Core.Ops.Arith.t_Rem Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_rem_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_rem_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: Core.Ops.Arith.t_Rem Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_rem_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_rem_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Ops.Arith.t_Sub Core.Primitive.t_u8 Core.Primitive.t_u8 =
  {
    f_Output = Core.Primitive.t_u8;
    f_sub_pre = (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) (out: Core.Primitive.t_u8) -> true
    );
    f_sub
    =
    fun (self: Core.Primitive.t_u8) (other: Core.Primitive.t_u8) ->
      Core.Primitive.C_u8 (self.Core.Primitive._0 -! other.Core.Primitive._0) <: Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Ops.Arith.t_Sub Core.Primitive.t_u16 Core.Primitive.t_u16 =
  {
    f_Output = Core.Primitive.t_u16;
    f_sub_pre = (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) (out: Core.Primitive.t_u16) ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_u16) (other: Core.Primitive.t_u16) ->
      Core.Primitive.C_u16 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Ops.Arith.t_Sub Core.Primitive.t_u32 Core.Primitive.t_u32 =
  {
    f_Output = Core.Primitive.t_u32;
    f_sub_pre = (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) (out: Core.Primitive.t_u32) ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_u32) (other: Core.Primitive.t_u32) ->
      Core.Primitive.C_u32 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Ops.Arith.t_Sub Core.Primitive.t_u64 Core.Primitive.t_u64 =
  {
    f_Output = Core.Primitive.t_u64;
    f_sub_pre = (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) -> true);
    f_sub_post
    =
    (fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) (out: Core.Primitive.t_u64) ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_u64) (other: Core.Primitive.t_u64) ->
      Core.Primitive.C_u64 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Ops.Arith.t_Sub Core.Primitive.t_u128 Core.Primitive.t_u128 =
  {
    f_Output = Core.Primitive.t_u128;
    f_sub_pre = (fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) -> true);
    f_sub_post
    =
    (fun
        (self: Core.Primitive.t_u128)
        (other: Core.Primitive.t_u128)
        (out: Core.Primitive.t_u128)
        ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_u128) (other: Core.Primitive.t_u128) ->
      Core.Primitive.C_u128 (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Ops.Arith.t_Sub Core.Primitive.t_usize Core.Primitive.t_usize =
  {
    f_Output = Core.Primitive.t_usize;
    f_sub_pre = (fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) -> true);
    f_sub_post
    =
    (fun
        (self: Core.Primitive.t_usize)
        (other: Core.Primitive.t_usize)
        (out: Core.Primitive.t_usize)
        ->
        true);
    f_sub
    =
    fun (self: Core.Primitive.t_usize) (other: Core.Primitive.t_usize) ->
      Core.Primitive.C_usize (self.Core.Primitive._0 -! other.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: Core.Ops.Arith.t_Div Core.Primitive.t_i8 Core.Primitive.t_i8 =
  {
    f_Output = Core.Primitive.t_i8;
    f_div_pre = (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) (out: Core.Primitive.t_i8) -> true
    );
    f_div
    =
    fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) ->
      Core.Primitive.C_i8 (self.Core.Primitive._0 /! other.Core.Primitive._0) <: Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Ops.Arith.t_Div Core.Primitive.t_i16 Core.Primitive.t_i16 =
  {
    f_Output = Core.Primitive.t_i16;
    f_div_pre = (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) (out: Core.Primitive.t_i16) ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) ->
      Core.Primitive.C_i16 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Ops.Arith.t_Div Core.Primitive.t_i32 Core.Primitive.t_i32 =
  {
    f_Output = Core.Primitive.t_i32;
    f_div_pre = (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) (out: Core.Primitive.t_i32) ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) ->
      Core.Primitive.C_i32 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Ops.Arith.t_Div Core.Primitive.t_i64 Core.Primitive.t_i64 =
  {
    f_Output = Core.Primitive.t_i64;
    f_div_pre = (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) -> true);
    f_div_post
    =
    (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) (out: Core.Primitive.t_i64) ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) ->
      Core.Primitive.C_i64 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Ops.Arith.t_Div Core.Primitive.t_i128 Core.Primitive.t_i128 =
  {
    f_Output = Core.Primitive.t_i128;
    f_div_pre = (fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) -> true);
    f_div_post
    =
    (fun
        (self: Core.Primitive.t_i128)
        (other: Core.Primitive.t_i128)
        (out: Core.Primitive.t_i128)
        ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) ->
      Core.Primitive.C_i128 (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: Core.Ops.Arith.t_Div Core.Primitive.t_isize Core.Primitive.t_isize =
  {
    f_Output = Core.Primitive.t_isize;
    f_div_pre = (fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) -> true);
    f_div_post
    =
    (fun
        (self: Core.Primitive.t_isize)
        (other: Core.Primitive.t_isize)
        (out: Core.Primitive.t_isize)
        ->
        true);
    f_div
    =
    fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) ->
      Core.Primitive.C_isize (self.Core.Primitive._0 /! other.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: Core.Ops.Arith.t_Rem Core.Primitive.t_i8 Core.Primitive.t_i8 =
  {
    f_Output = Core.Primitive.t_i8;
    f_rem_pre = (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) (out: Core.Primitive.t_i8) -> true
    );
    f_rem
    =
    fun (self: Core.Primitive.t_i8) (other: Core.Primitive.t_i8) ->
      Core.Primitive.C_i8 (self.Core.Primitive._0 %! other.Core.Primitive._0) <: Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: Core.Ops.Arith.t_Rem Core.Primitive.t_i16 Core.Primitive.t_i16 =
  {
    f_Output = Core.Primitive.t_i16;
    f_rem_pre = (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) (out: Core.Primitive.t_i16) ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_i16) (other: Core.Primitive.t_i16) ->
      Core.Primitive.C_i16 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: Core.Ops.Arith.t_Rem Core.Primitive.t_i32 Core.Primitive.t_i32 =
  {
    f_Output = Core.Primitive.t_i32;
    f_rem_pre = (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) (out: Core.Primitive.t_i32) ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_i32) (other: Core.Primitive.t_i32) ->
      Core.Primitive.C_i32 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: Core.Ops.Arith.t_Rem Core.Primitive.t_i64 Core.Primitive.t_i64 =
  {
    f_Output = Core.Primitive.t_i64;
    f_rem_pre = (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) -> true);
    f_rem_post
    =
    (fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) (out: Core.Primitive.t_i64) ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_i64) (other: Core.Primitive.t_i64) ->
      Core.Primitive.C_i64 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: Core.Ops.Arith.t_Rem Core.Primitive.t_i128 Core.Primitive.t_i128 =
  {
    f_Output = Core.Primitive.t_i128;
    f_rem_pre = (fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) -> true);
    f_rem_post
    =
    (fun
        (self: Core.Primitive.t_i128)
        (other: Core.Primitive.t_i128)
        (out: Core.Primitive.t_i128)
        ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_i128) (other: Core.Primitive.t_i128) ->
      Core.Primitive.C_i128 (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: Core.Ops.Arith.t_Rem Core.Primitive.t_isize Core.Primitive.t_isize =
  {
    f_Output = Core.Primitive.t_isize;
    f_rem_pre = (fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) -> true);
    f_rem_post
    =
    (fun
        (self: Core.Primitive.t_isize)
        (other: Core.Primitive.t_isize)
        (out: Core.Primitive.t_isize)
        ->
        true);
    f_rem
    =
    fun (self: Core.Primitive.t_isize) (other: Core.Primitive.t_isize) ->
      Core.Primitive.C_isize (self.Core.Primitive._0 %! other.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }
