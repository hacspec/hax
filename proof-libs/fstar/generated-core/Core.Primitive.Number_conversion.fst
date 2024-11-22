module Core.Primitive.Number_conversion
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From Core.Primitive.t_u128 u128 =
  {
    f_from_pre = (fun (x: u128) -> true);
    f_from_post = (fun (x: u128) (out: Core.Primitive.t_u128) -> true);
    f_from
    =
    fun (x: u128) ->
      Core.Primitive.C_u128
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u128
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U128)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From u128 Core.Primitive.t_u128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u128) (out: u128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u128) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u128
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From Core.Primitive.t_u16 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: Core.Primitive.t_u16) -> true);
    f_from
    =
    fun (x: u16) ->
      Core.Primitive.C_u16
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u16
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U16)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From u16 Core.Primitive.t_u16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u16) (out: u16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u16) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u16
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From Core.Primitive.t_u32 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: Core.Primitive.t_u32) -> true);
    f_from
    =
    fun (x: u32) ->
      Core.Primitive.C_u32
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u32
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U32)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From u32 Core.Primitive.t_u32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u32) (out: u32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u32) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u32
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From Core.Primitive.t_u64 u64 =
  {
    f_from_pre = (fun (x: u64) -> true);
    f_from_post = (fun (x: u64) (out: Core.Primitive.t_u64) -> true);
    f_from
    =
    fun (x: u64) ->
      Core.Primitive.C_u64
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u64
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U64)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From u64 Core.Primitive.t_u64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u64) (out: u64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u64) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u64
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From Core.Primitive.t_u8 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: Core.Primitive.t_u8) -> true);
    f_from
    =
    fun (x: u8) ->
      Core.Primitive.C_u8
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u8 #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_U8)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From u8 Core.Primitive.t_u8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u8) (out: u8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u8) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u8
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From Core.Primitive.t_usize usize =
  {
    f_from_pre = (fun (x: usize) -> true);
    f_from_post = (fun (x: usize) (out: Core.Primitive.t_usize) -> true);
    f_from
    =
    fun (x: usize) ->
      Core.Primitive.C_usize
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #usize
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U64)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From usize Core.Primitive.t_usize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_usize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_usize) (out: usize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_usize) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #usize
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Convert.t_From Core.Primitive.t_usize Core.Primitive.t_u64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u64) (out: Core.Primitive.t_usize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u64) ->
      Core.Primitive.C_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Convert.t_From Core.Primitive.t_u64 Core.Primitive.t_usize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_usize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_usize) (out: Core.Primitive.t_u64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_usize) ->
      Core.Primitive.C_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From Core.Primitive.t_u16 Core.Primitive.t_u8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u8) (out: Core.Primitive.t_u16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u8) ->
      Core.Primitive.C_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From Core.Primitive.t_u32 Core.Primitive.t_u8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u8) (out: Core.Primitive.t_u32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u8) ->
      Core.Primitive.C_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From Core.Primitive.t_u64 Core.Primitive.t_u8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u8) (out: Core.Primitive.t_u64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u8) ->
      Core.Primitive.C_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From Core.Primitive.t_u128 Core.Primitive.t_u8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u8) (out: Core.Primitive.t_u128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u8) ->
      Core.Primitive.C_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From Core.Primitive.t_usize Core.Primitive.t_u8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u8) (out: Core.Primitive.t_usize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u8) ->
      Core.Primitive.C_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From Core.Primitive.t_u8 Core.Primitive.t_u16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u16) (out: Core.Primitive.t_u8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u16) ->
      Core.Primitive.C_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From Core.Primitive.t_u32 Core.Primitive.t_u16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u16) (out: Core.Primitive.t_u32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u16) ->
      Core.Primitive.C_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From Core.Primitive.t_u64 Core.Primitive.t_u16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u16) (out: Core.Primitive.t_u64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u16) ->
      Core.Primitive.C_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From Core.Primitive.t_u128 Core.Primitive.t_u16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u16) (out: Core.Primitive.t_u128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u16) ->
      Core.Primitive.C_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Convert.t_From Core.Primitive.t_usize Core.Primitive.t_u16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u16) (out: Core.Primitive.t_usize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u16) ->
      Core.Primitive.C_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From Core.Primitive.t_u8 Core.Primitive.t_u32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u32) (out: Core.Primitive.t_u8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u32) ->
      Core.Primitive.C_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From Core.Primitive.t_u16 Core.Primitive.t_u32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u32) (out: Core.Primitive.t_u16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u32) ->
      Core.Primitive.C_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Convert.t_From Core.Primitive.t_u64 Core.Primitive.t_u32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u32) (out: Core.Primitive.t_u64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u32) ->
      Core.Primitive.C_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Convert.t_From Core.Primitive.t_u128 Core.Primitive.t_u32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u32) (out: Core.Primitive.t_u128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u32) ->
      Core.Primitive.C_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Convert.t_From Core.Primitive.t_usize Core.Primitive.t_u32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u32) (out: Core.Primitive.t_usize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u32) ->
      Core.Primitive.C_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Convert.t_From Core.Primitive.t_u8 Core.Primitive.t_u64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u64) (out: Core.Primitive.t_u8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u64) ->
      Core.Primitive.C_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Convert.t_From Core.Primitive.t_u16 Core.Primitive.t_u64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u64) (out: Core.Primitive.t_u16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u64) ->
      Core.Primitive.C_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Convert.t_From Core.Primitive.t_u32 Core.Primitive.t_u64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u64) (out: Core.Primitive.t_u32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u64) ->
      Core.Primitive.C_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Convert.t_From Core.Primitive.t_u128 Core.Primitive.t_u64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u64) (out: Core.Primitive.t_u128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u64) ->
      Core.Primitive.C_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Convert.t_From Core.Primitive.t_u8 Core.Primitive.t_u128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u128) (out: Core.Primitive.t_u8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u128) ->
      Core.Primitive.C_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Convert.t_From Core.Primitive.t_u16 Core.Primitive.t_u128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u128) (out: Core.Primitive.t_u16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u128) ->
      Core.Primitive.C_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Convert.t_From Core.Primitive.t_u32 Core.Primitive.t_u128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u128) (out: Core.Primitive.t_u32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u128) ->
      Core.Primitive.C_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Convert.t_From Core.Primitive.t_u64 Core.Primitive.t_u128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u128) (out: Core.Primitive.t_u64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u128) ->
      Core.Primitive.C_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Convert.t_From Core.Primitive.t_usize Core.Primitive.t_u128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_u128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_u128) (out: Core.Primitive.t_usize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_u128) ->
      Core.Primitive.C_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Convert.t_From Core.Primitive.t_u8 Core.Primitive.t_usize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_usize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_usize) (out: Core.Primitive.t_u8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_usize) ->
      Core.Primitive.C_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Convert.t_From Core.Primitive.t_u16 Core.Primitive.t_usize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_usize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_usize) (out: Core.Primitive.t_u16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_usize) ->
      Core.Primitive.C_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Convert.t_From Core.Primitive.t_u32 Core.Primitive.t_usize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_usize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_usize) (out: Core.Primitive.t_u32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_usize) ->
      Core.Primitive.C_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Convert.t_From Core.Primitive.t_u128 Core.Primitive.t_usize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_usize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_usize) (out: Core.Primitive.t_u128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_usize) ->
      Core.Primitive.C_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_u128
  }
