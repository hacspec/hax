module Core.Primitive.Number_conversion_i
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From Core.Primitive.t_i8 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: Core.Primitive.t_i8) -> true);
    f_from
    =
    fun (x: i8) ->
      Core.Primitive.C_i8
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i8 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I8)
      <:
      Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From i8 Core.Primitive.t_i8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i8) (out: i8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i8) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i8
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From Core.Primitive.t_i16 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: Core.Primitive.t_i16) -> true);
    f_from
    =
    fun (x: i16) ->
      Core.Primitive.C_i16
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i16 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I16)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From i16 Core.Primitive.t_i16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i16) (out: i16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i16) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i16
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From Core.Primitive.t_i32 i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: Core.Primitive.t_i32) -> true);
    f_from
    =
    fun (x: i32) ->
      Core.Primitive.C_i32
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i32 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I32)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From i32 Core.Primitive.t_i32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i32) (out: i32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i32) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i32
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From Core.Primitive.t_i64 i64 =
  {
    f_from_pre = (fun (x: i64) -> true);
    f_from_post = (fun (x: i64) (out: Core.Primitive.t_i64) -> true);
    f_from
    =
    fun (x: i64) ->
      Core.Primitive.C_i64
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i64 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I64)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From i64 Core.Primitive.t_i64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i64) (out: i64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i64) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i64
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From Core.Primitive.t_i128 i128 =
  {
    f_from_pre = (fun (x: i128) -> true);
    f_from_post = (fun (x: i128) (out: Core.Primitive.t_i128) -> true);
    f_from
    =
    fun (x: i128) ->
      Core.Primitive.C_i128
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i128 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I128)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From i128 Core.Primitive.t_i128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i128) (out: i128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i128) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i128
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From Core.Primitive.t_isize isize =
  {
    f_from_pre = (fun (x: isize) -> true);
    f_from_post = (fun (x: isize) (out: Core.Primitive.t_isize) -> true);
    f_from
    =
    fun (x: isize) ->
      Core.Primitive.C_isize
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #isize #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I64)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From isize Core.Primitive.t_isize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_isize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_isize) (out: isize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_isize) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #isize
        #FStar.Tactics.Typeclasses.solve
        x.Core.Primitive._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From Core.Primitive.t_i16 Core.Primitive.t_i8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i8) (out: Core.Primitive.t_i16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i8) ->
      Core.Primitive.C_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From Core.Primitive.t_i32 Core.Primitive.t_i8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i8) (out: Core.Primitive.t_i32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i8) ->
      Core.Primitive.C_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From Core.Primitive.t_i64 Core.Primitive.t_i8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i8) (out: Core.Primitive.t_i64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i8) ->
      Core.Primitive.C_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From Core.Primitive.t_i128 Core.Primitive.t_i8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i8) (out: Core.Primitive.t_i128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i8) ->
      Core.Primitive.C_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From Core.Primitive.t_isize Core.Primitive.t_i8 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i8) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i8) (out: Core.Primitive.t_isize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i8) ->
      Core.Primitive.C_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From Core.Primitive.t_i8 Core.Primitive.t_i16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i16) (out: Core.Primitive.t_i8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i16) ->
      Core.Primitive.C_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From Core.Primitive.t_i32 Core.Primitive.t_i16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i16) (out: Core.Primitive.t_i32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i16) ->
      Core.Primitive.C_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From Core.Primitive.t_i64 Core.Primitive.t_i16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i16) (out: Core.Primitive.t_i64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i16) ->
      Core.Primitive.C_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From Core.Primitive.t_i128 Core.Primitive.t_i16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i16) (out: Core.Primitive.t_i128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i16) ->
      Core.Primitive.C_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Convert.t_From Core.Primitive.t_isize Core.Primitive.t_i16 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i16) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i16) (out: Core.Primitive.t_isize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i16) ->
      Core.Primitive.C_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From Core.Primitive.t_i8 Core.Primitive.t_i32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i32) (out: Core.Primitive.t_i8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i32) ->
      Core.Primitive.C_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From Core.Primitive.t_i16 Core.Primitive.t_i32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i32) (out: Core.Primitive.t_i16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i32) ->
      Core.Primitive.C_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Convert.t_From Core.Primitive.t_i64 Core.Primitive.t_i32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i32) (out: Core.Primitive.t_i64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i32) ->
      Core.Primitive.C_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Convert.t_From Core.Primitive.t_i128 Core.Primitive.t_i32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i32) (out: Core.Primitive.t_i128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i32) ->
      Core.Primitive.C_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Convert.t_From Core.Primitive.t_isize Core.Primitive.t_i32 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i32) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i32) (out: Core.Primitive.t_isize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i32) ->
      Core.Primitive.C_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Convert.t_From Core.Primitive.t_i8 Core.Primitive.t_i64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i64) (out: Core.Primitive.t_i8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i64) ->
      Core.Primitive.C_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Convert.t_From Core.Primitive.t_i16 Core.Primitive.t_i64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i64) (out: Core.Primitive.t_i16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i64) ->
      Core.Primitive.C_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Convert.t_From Core.Primitive.t_i32 Core.Primitive.t_i64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i64) (out: Core.Primitive.t_i32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i64) ->
      Core.Primitive.C_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Convert.t_From Core.Primitive.t_i128 Core.Primitive.t_i64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i64) (out: Core.Primitive.t_i128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i64) ->
      Core.Primitive.C_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Convert.t_From Core.Primitive.t_isize Core.Primitive.t_i64 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i64) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i64) (out: Core.Primitive.t_isize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i64) ->
      Core.Primitive.C_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Convert.t_From Core.Primitive.t_i8 Core.Primitive.t_i128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i128) (out: Core.Primitive.t_i8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i128) ->
      Core.Primitive.C_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Convert.t_From Core.Primitive.t_i16 Core.Primitive.t_i128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i128) (out: Core.Primitive.t_i16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i128) ->
      Core.Primitive.C_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Convert.t_From Core.Primitive.t_i32 Core.Primitive.t_i128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i128) (out: Core.Primitive.t_i32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i128) ->
      Core.Primitive.C_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Convert.t_From Core.Primitive.t_i64 Core.Primitive.t_i128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i128) (out: Core.Primitive.t_i64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i128) ->
      Core.Primitive.C_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Convert.t_From Core.Primitive.t_isize Core.Primitive.t_i128 =
  {
    f_from_pre = (fun (x: Core.Primitive.t_i128) -> true);
    f_from_post = (fun (x: Core.Primitive.t_i128) (out: Core.Primitive.t_isize) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_i128) ->
      Core.Primitive.C_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Convert.t_From Core.Primitive.t_i8 Core.Primitive.t_isize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_isize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_isize) (out: Core.Primitive.t_i8) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_isize) ->
      Core.Primitive.C_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Convert.t_From Core.Primitive.t_i16 Core.Primitive.t_isize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_isize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_isize) (out: Core.Primitive.t_i16) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_isize) ->
      Core.Primitive.C_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Convert.t_From Core.Primitive.t_i32 Core.Primitive.t_isize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_isize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_isize) (out: Core.Primitive.t_i32) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_isize) ->
      Core.Primitive.C_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Convert.t_From Core.Primitive.t_i64 Core.Primitive.t_isize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_isize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_isize) (out: Core.Primitive.t_i64) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_isize) ->
      Core.Primitive.C_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Convert.t_From Core.Primitive.t_i128 Core.Primitive.t_isize =
  {
    f_from_pre = (fun (x: Core.Primitive.t_isize) -> true);
    f_from_post = (fun (x: Core.Primitive.t_isize) (out: Core.Primitive.t_i128) -> true);
    f_from
    =
    fun (x: Core.Primitive.t_isize) ->
      Core.Primitive.C_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0)
      <:
      Core.Primitive.t_i128
  }
