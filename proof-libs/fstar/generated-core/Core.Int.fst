module Core.Int
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Core.Ops.Arith
open Core.Ops.Bit
open Core.Cmp

class t_Constants (v_Self: Type0) = {
  f_ZERO:v_Self;
  f_ONE:v_Self;
  f_MIN:v_Self;
  f_MAX:v_Self
}

let impl_21__WORDSIZE: Core.Base.Int.t_HaxInt = Core.Base.Int.Base_spec.v_WORDSIZE_8_

let impl_48__WORDSIZE: Core.Base.Int.t_HaxInt = Core.Base.Int.Base_spec.v_WORDSIZE_16_

let impl_75__WORDSIZE: Core.Base.Int.t_HaxInt = Core.Base.Int.Base_spec.v_WORDSIZE_32_

let impl_102__WORDSIZE: Core.Base.Int.t_HaxInt = Core.Base.Int.Base_spec.v_WORDSIZE_64_

let impl_129__WORDSIZE: Core.Base.Int.t_HaxInt = Core.Base.Int.Base_spec.v_WORDSIZE_128_

type t_HaxInt_U128 = x:Core.Base.Int.t_HaxInt{x < pow2 128}
type t_U128 = { f_v:t_HaxInt_U128 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_128: t_Constants t_U128 =
  {
    f_ZERO = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U128;
    f_ONE = { f_v = Core.Base.Int.Base_spec.impl_9__ONE } <: t_U128;
    f_MIN = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U128;
    f_MAX = { f_v = Core.Base.Int.Base_spec.v_WORDSIZE_128_SUB_1_ } <: t_U128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_135: Core.Clone.t_Clone t_U128 =
  {
    f_clone_pre = (fun (self: t_U128) -> true);
    f_clone_post = (fun (self: t_U128) (out: t_U128) -> true);
    f_clone
    =
    fun (self: t_U128) ->
      { f_v = Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_U128
  }

type t_HaxInt_U16 = x:Core.Base.Int.t_HaxInt{x < pow2 16}
type t_U16 = { f_v:t_HaxInt_U16 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: t_Constants t_U16 =
  {
    f_ZERO = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U16;
    f_ONE = { f_v = Core.Base.Int.Base_spec.impl_9__ONE } <: t_U16;
    f_MIN = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U16;
    f_MAX = { f_v = Core.Base.Int.Base_spec.v_WORDSIZE_16_SUB_1_ } <: t_U16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: Core.Clone.t_Clone t_U16 =
  {
    f_clone_pre = (fun (self: t_U16) -> true);
    f_clone_post = (fun (self: t_U16) (out: t_U16) -> true);
    f_clone
    =
    fun (self: t_U16) ->
      { f_v = Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_U16
  }

type t_HaxInt_U32 = x:Core.Base.Int.t_HaxInt{x < pow2 32}
type t_U32 = { f_v:t_HaxInt_U32 }

let impl_21__BITS: t_U32 = { f_v = Core.Base.Int.Base_spec.v_BITS_8_ } <: t_U32

let impl_48__BITS: t_U32 = { f_v = Core.Base.Int.Base_spec.v_BITS_16_ } <: t_U32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_74: t_Constants t_U32 =
  {
    f_ZERO = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U32;
    f_ONE = { f_v = Core.Base.Int.Base_spec.impl_9__ONE } <: t_U32;
    f_MIN = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U32;
    f_MAX = { f_v = Core.Base.Int.Base_spec.v_WORDSIZE_32_SUB_1_ } <: t_U32
  }

let impl_75__BITS: t_U32 = { f_v = Core.Base.Int.Base_spec.v_BITS_32_ } <: t_U32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_81: Core.Clone.t_Clone t_U32 =
  {
    f_clone_pre = (fun (self: t_U32) -> true);
    f_clone_post = (fun (self: t_U32) (out: t_U32) -> true);
    f_clone
    =
    fun (self: t_U32) ->
      { f_v = Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_U32
  }

let impl_102__BITS: t_U32 = { f_v = Core.Base.Int.Base_spec.v_BITS_64_ } <: t_U32

let impl_129__BITS: t_U32 = { f_v = Core.Base.Int.Base_spec.v_BITS_128_ } <: t_U32

type t_HaxInt_U64 = x:Core.Base.Int.t_HaxInt{x < pow2 64}
type t_U64 = { f_v:t_HaxInt_U64 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_101: t_Constants t_U64 =
  {
    f_ZERO = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U64;
    f_ONE = { f_v = Core.Base.Int.Base_spec.impl_9__ONE } <: t_U64;
    f_MIN = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U64;
    f_MAX = { f_v = Core.Base.Int.Base_spec.v_WORDSIZE_64_SUB_1_ } <: t_U64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_108: Core.Clone.t_Clone t_U64 =
  {
    f_clone_pre = (fun (self: t_U64) -> true);
    f_clone_post = (fun (self: t_U64) (out: t_U64) -> true);
    f_clone
    =
    fun (self: t_U64) ->
      { f_v = Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_U64
  }

type t_HaxInt_U8 = x:Core.Base.Int.t_HaxInt{x < pow2 8}
type t_U8 = { f_v:t_HaxInt_U8 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: t_Constants t_U8 =
  {
    f_ZERO = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U8;
    f_ONE = { f_v = Core.Base.Int.Base_spec.impl_9__ONE } <: t_U8;
    f_MIN = { f_v = Core.Base.Int.Base_spec.impl_9__ZERO } <: t_U8;
    f_MAX = { f_v = Core.Base.Int.Base_spec.v_WORDSIZE_8_SUB_1_ } <: t_U8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Clone.t_Clone t_U8 =
  {
    f_clone_pre = (fun (self: t_U8) -> true);
    f_clone_post = (fun (self: t_U8) (out: t_U8) -> true);
    f_clone
    =
    fun (self: t_U8) ->
      { f_v = Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_U8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Coerce.t_Abstraction t_U8 =
  {
    f_AbstractType = Core.Base.Int.t_HaxInt;
    f_lift_pre = (fun (self: t_U8) -> true);
    f_lift_post = (fun (self: t_U8) (out: Core.Base.Int.t_HaxInt) -> true);
    f_lift = fun (self: t_U8) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Cmp.t_PartialEq t_U8 t_U8 =
  {
    f_eq_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_eq_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        (Core.Coerce.f_lift #t_U8
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U8
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
          <:
          Core.Base.Int.t_HaxInt));
    f_ne_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_ne_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U8) (rhs: t_U8) ->
      ~.((Core.Coerce.f_lift #t_U8
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U8
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
          <:
          Core.Base.Int.t_HaxInt)
        <:
        bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Cmp.t_PartialOrd t_U8 t_U8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U8) (rhs: t_U8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
            <:
            Core.Base.Int.t_HaxInt));
    f_lt_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_lt_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_le_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_gt_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_ge_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U8) (rhs: t_U8) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
            <:
            Core.Base.Int.t_HaxInt)
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Coerce.t_Abstraction t_U16 =
  {
    f_AbstractType = Core.Base.Int.t_HaxInt;
    f_lift_pre = (fun (self: t_U16) -> true);
    f_lift_post = (fun (self: t_U16) (out: Core.Base.Int.t_HaxInt) -> true);
    f_lift = fun (self: t_U16) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: Core.Cmp.t_PartialEq t_U16 t_U16 =
  {
    f_eq_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_eq_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        (Core.Coerce.f_lift #t_U16
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U16
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
          <:
          Core.Base.Int.t_HaxInt));
    f_ne_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_ne_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U16) (rhs: t_U16) ->
      ~.((Core.Coerce.f_lift #t_U16
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U16
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
          <:
          Core.Base.Int.t_HaxInt)
        <:
        bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: Core.Cmp.t_PartialOrd t_U16 t_U16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U16) (rhs: t_U16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
            <:
            Core.Base.Int.t_HaxInt));
    f_lt_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_lt_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_le_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_gt_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_ge_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U16) (rhs: t_U16) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
            <:
            Core.Base.Int.t_HaxInt)
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_76: Core.Coerce.t_Abstraction t_U32 =
  {
    f_AbstractType = Core.Base.Int.t_HaxInt;
    f_lift_pre = (fun (self: t_U32) -> true);
    f_lift_post = (fun (self: t_U32) (out: Core.Base.Int.t_HaxInt) -> true);
    f_lift = fun (self: t_U32) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_82: Core.Cmp.t_PartialEq t_U32 t_U32 =
  {
    f_eq_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_eq_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        (Core.Coerce.f_lift #t_U32
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U32
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
          <:
          Core.Base.Int.t_HaxInt));
    f_ne_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_ne_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U32) (rhs: t_U32) ->
      ~.((Core.Coerce.f_lift #t_U32
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U32
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
          <:
          Core.Base.Int.t_HaxInt)
        <:
        bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_83: Core.Cmp.t_PartialOrd t_U32 t_U32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U32) (rhs: t_U32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
            <:
            Core.Base.Int.t_HaxInt));
    f_lt_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_lt_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_le_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_gt_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_ge_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U32) (rhs: t_U32) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
            <:
            Core.Base.Int.t_HaxInt)
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_103: Core.Coerce.t_Abstraction t_U64 =
  {
    f_AbstractType = Core.Base.Int.t_HaxInt;
    f_lift_pre = (fun (self: t_U64) -> true);
    f_lift_post = (fun (self: t_U64) (out: Core.Base.Int.t_HaxInt) -> true);
    f_lift = fun (self: t_U64) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_109: Core.Cmp.t_PartialEq t_U64 t_U64 =
  {
    f_eq_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_eq_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        (Core.Coerce.f_lift #t_U64
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U64
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
          <:
          Core.Base.Int.t_HaxInt));
    f_ne_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_ne_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U64) (rhs: t_U64) ->
      ~.((Core.Coerce.f_lift #t_U64
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U64
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
          <:
          Core.Base.Int.t_HaxInt)
        <:
        bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_110: Core.Cmp.t_PartialOrd t_U64 t_U64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U64) (rhs: t_U64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
            <:
            Core.Base.Int.t_HaxInt));
    f_lt_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_lt_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_le_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_gt_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_ge_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U64) (rhs: t_U64) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
            <:
            Core.Base.Int.t_HaxInt)
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_130: Core.Coerce.t_Abstraction t_U128 =
  {
    f_AbstractType = Core.Base.Int.t_HaxInt;
    f_lift_pre = (fun (self: t_U128) -> true);
    f_lift_post = (fun (self: t_U128) (out: Core.Base.Int.t_HaxInt) -> true);
    f_lift = fun (self: t_U128) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_136: Core.Cmp.t_PartialEq t_U128 t_U128 =
  {
    f_eq_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_eq_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        (Core.Coerce.f_lift #t_U128
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U128
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
          <:
          Core.Base.Int.t_HaxInt));
    f_ne_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_ne_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U128) (rhs: t_U128) ->
      ~.((Core.Coerce.f_lift #t_U128
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
          <:
          Core.Base.Int.t_HaxInt) =.
        (Core.Coerce.f_lift #t_U128
            #FStar.Tactics.Typeclasses.solve
            (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
          <:
          Core.Base.Int.t_HaxInt)
        <:
        bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_137: Core.Cmp.t_PartialOrd t_U128 t_U128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U128) (rhs: t_U128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
            <:
            Core.Base.Int.t_HaxInt));
    f_lt_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_lt_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_le_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_gt_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
            #Core.Base.Int.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Int.t_HaxInt)
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_ge_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U128) (rhs: t_U128) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base.Int.t_HaxInt
          #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          (Core.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
            <:
            Core.Base.Int.t_HaxInt)
          (Core.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
            <:
            Core.Base.Int.t_HaxInt)
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Coerce.t_Concretization Core.Base.Int.t_HaxInt t_U8 =
  {
    f_concretize_pre = (fun (self: Core.Base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Int.t_HaxInt) (out: t_U8) -> true);
    f_concretize
    =
    fun (self: Core.Base.Int.t_HaxInt) ->
      { f_v = Core.Base.Int.Base_impl.impl_10__rem self Core.Base.Int.Base_spec.v_WORDSIZE_8_ }
      <:
      t_U8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From t_U8 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From t_U8 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From t_U8 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From t_U8 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Coerce.t_Concretization Core.Base.Int.t_HaxInt t_U16 =
  {
    f_concretize_pre = (fun (self: Core.Base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Int.t_HaxInt) (out: t_U16) -> true);
    f_concretize
    =
    fun (self: Core.Base.Int.t_HaxInt) ->
      { f_v = Core.Base.Int.Base_impl.impl_10__rem self Core.Base.Int.Base_spec.v_WORDSIZE_16_ }
      <:
      t_U16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_U16 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From t_U16 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From t_U16 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From t_U16 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_77: Core.Coerce.t_Concretization Core.Base.Int.t_HaxInt t_U32 =
  {
    f_concretize_pre = (fun (self: Core.Base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Int.t_HaxInt) (out: t_U32) -> true);
    f_concretize
    =
    fun (self: Core.Base.Int.t_HaxInt) ->
      { f_v = Core.Base.Int.Base_impl.impl_10__rem self Core.Base.Int.Base_spec.v_WORDSIZE_32_ }
      <:
      t_U32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_U32 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From t_U32 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From t_U32 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From t_U32 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_104: Core.Coerce.t_Concretization Core.Base.Int.t_HaxInt t_U64 =
  {
    f_concretize_pre = (fun (self: Core.Base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Int.t_HaxInt) (out: t_U64) -> true);
    f_concretize
    =
    fun (self: Core.Base.Int.t_HaxInt) ->
      { f_v = Core.Base.Int.Base_impl.impl_10__rem self Core.Base.Int.Base_spec.v_WORDSIZE_64_ }
      <:
      t_U64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From t_U64 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From t_U64 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From t_U64 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From t_U64 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_131: Core.Coerce.t_Concretization Core.Base.Int.t_HaxInt t_U128 =
  {
    f_concretize_pre = (fun (self: Core.Base.Int.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Int.t_HaxInt) (out: t_U128) -> true);
    f_concretize
    =
    fun (self: Core.Base.Int.t_HaxInt) ->
      { f_v = Core.Base.Int.Base_impl.impl_10__rem self Core.Base.Int.Base_spec.v_WORDSIZE_128_ }
      <:
      t_U128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From t_U128 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From t_U128 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From t_U128 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From t_U128 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x <: Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Ops.Arith.t_Neg t_U8 =
  {
    f_Output = t_U8;
    f_neg_pre = (fun (self: t_U8) -> true);
    f_neg_post = (fun (self: t_U8) (out: t_U8) -> true);
    f_neg
    =
    fun (self: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_7__sub Core.Base.Int.Base_spec.v_WORDSIZE_8_
            (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U8
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Int.t_HaxInt)
                Core.Base.Int.Base_spec.v_WORDSIZE_8_
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Ops.Arith.t_Mul t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_mul_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_mul_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_mul
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_11__mul (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Ops.Arith.t_Rem t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_rem_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_rem_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_rem
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Ops.Arith.t_Add t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_add_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_add_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_add
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Ops.Arith.t_Div t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_div_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_div_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_div
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__div (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Ops.Bit.t_Shl t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Ops.Bit.t_Shl t_U8 t_U16 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U16) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Ops.Bit.t_Shl t_U8 t_U32 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U32) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Ops.Bit.t_Shl t_U8 t_U64 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U64) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Ops.Bit.t_Shl t_U8 t_U128 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U128) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Ops.Bit.t_Shr t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Ops.Bit.t_Shr t_U8 t_U16 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U16) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Ops.Bit.t_Shr t_U8 t_U32 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U32) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Ops.Bit.t_Shr t_U8 t_U64 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U64) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Ops.Bit.t_Shr t_U8 t_U128 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U128) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Ops.Bit.t_BitXor t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_bitxor_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_bitxor_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_bitxor
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_14__bitxor (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Ops.Bit.t_BitAnd t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_bitand_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_bitand_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_bitand
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_15__bitand (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Ops.Bit.t_BitOr t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_bitor_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_bitor_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_bitor
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_16__bitor (Core.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Ops.Arith.t_Neg t_U16 =
  {
    f_Output = t_U16;
    f_neg_pre = (fun (self: t_U16) -> true);
    f_neg_post = (fun (self: t_U16) (out: t_U16) -> true);
    f_neg
    =
    fun (self: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_7__sub Core.Base.Int.Base_spec.v_WORDSIZE_16_
            (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U16
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Int.t_HaxInt)
                Core.Base.Int.Base_spec.v_WORDSIZE_16_
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: Core.Ops.Arith.t_Mul t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_mul_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_mul_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_mul
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_11__mul (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: Core.Ops.Arith.t_Rem t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_rem_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_rem_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_rem
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: Core.Ops.Arith.t_Add t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_add_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_add_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_add
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: Core.Ops.Arith.t_Div t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_div_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_div_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_div
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__div (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: Core.Ops.Bit.t_Shl t_U16 t_U8 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U8) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: Core.Ops.Bit.t_Shl t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: Core.Ops.Bit.t_Shl t_U16 t_U32 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U32) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: Core.Ops.Bit.t_Shl t_U16 t_U64 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U64) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: Core.Ops.Bit.t_Shl t_U16 t_U128 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U128) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_66: Core.Ops.Bit.t_Shr t_U16 t_U8 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U8) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_67: Core.Ops.Bit.t_Shr t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_68: Core.Ops.Bit.t_Shr t_U16 t_U32 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U32) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_69: Core.Ops.Bit.t_Shr t_U16 t_U64 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U64) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_70: Core.Ops.Bit.t_Shr t_U16 t_U128 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U128) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_71: Core.Ops.Bit.t_BitXor t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_bitxor_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_bitxor_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_bitxor
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_14__bitxor (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_72: Core.Ops.Bit.t_BitAnd t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_bitand_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_bitand_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_bitand
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_15__bitand (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_73: Core.Ops.Bit.t_BitOr t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_bitor_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_bitor_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_bitor
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_16__bitor (Core.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_78: Core.Ops.Arith.t_Neg t_U32 =
  {
    f_Output = t_U32;
    f_neg_pre = (fun (self: t_U32) -> true);
    f_neg_post = (fun (self: t_U32) (out: t_U32) -> true);
    f_neg
    =
    fun (self: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_7__sub Core.Base.Int.Base_spec.v_WORDSIZE_32_
            (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U32
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Int.t_HaxInt)
                Core.Base.Int.Base_spec.v_WORDSIZE_32_
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_84: Core.Ops.Arith.t_Mul t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_mul_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_mul_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_mul
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_11__mul (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_85: Core.Ops.Arith.t_Rem t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_rem_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_rem_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_rem
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_86: Core.Ops.Arith.t_Add t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_add_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_add_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_add
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_87: Core.Ops.Arith.t_Div t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_div_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_div_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_div
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__div (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_88: Core.Ops.Bit.t_Shl t_U32 t_U8 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U8) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_89: Core.Ops.Bit.t_Shl t_U32 t_U16 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U16) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_90: Core.Ops.Bit.t_Shl t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_91: Core.Ops.Bit.t_Shl t_U32 t_U64 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U64) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_92: Core.Ops.Bit.t_Shl t_U32 t_U128 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U128) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_93: Core.Ops.Bit.t_Shr t_U32 t_U8 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U8) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_94: Core.Ops.Bit.t_Shr t_U32 t_U16 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U16) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_95: Core.Ops.Bit.t_Shr t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_96: Core.Ops.Bit.t_Shr t_U32 t_U64 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U64) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_97: Core.Ops.Bit.t_Shr t_U32 t_U128 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U128) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_98: Core.Ops.Bit.t_BitXor t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_bitxor_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_bitxor_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_bitxor
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_14__bitxor (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_99: Core.Ops.Bit.t_BitAnd t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_bitand_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_bitand_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_bitand
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_15__bitand (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_100: Core.Ops.Bit.t_BitOr t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_bitor_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_bitor_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_bitor
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_16__bitor (Core.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_105: Core.Ops.Arith.t_Neg t_U64 =
  {
    f_Output = t_U64;
    f_neg_pre = (fun (self: t_U64) -> true);
    f_neg_post = (fun (self: t_U64) (out: t_U64) -> true);
    f_neg
    =
    fun (self: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_7__sub Core.Base.Int.Base_spec.v_WORDSIZE_64_
            (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U64
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Int.t_HaxInt)
                Core.Base.Int.Base_spec.v_WORDSIZE_64_
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_111: Core.Ops.Arith.t_Mul t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_mul_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_mul_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_mul
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_11__mul (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_112: Core.Ops.Arith.t_Rem t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_rem_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_rem_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_rem
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_113: Core.Ops.Arith.t_Add t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_add_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_add_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_add
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_114: Core.Ops.Arith.t_Div t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_div_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_div_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_div
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__div (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_115: Core.Ops.Bit.t_Shl t_U64 t_U8 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U8) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_116: Core.Ops.Bit.t_Shl t_U64 t_U16 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U16) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_117: Core.Ops.Bit.t_Shl t_U64 t_U32 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U32) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_118: Core.Ops.Bit.t_Shl t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_119: Core.Ops.Bit.t_Shl t_U64 t_U128 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U128) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_120: Core.Ops.Bit.t_Shr t_U64 t_U8 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U8) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_121: Core.Ops.Bit.t_Shr t_U64 t_U16 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U16) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_122: Core.Ops.Bit.t_Shr t_U64 t_U32 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U32) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_123: Core.Ops.Bit.t_Shr t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_124: Core.Ops.Bit.t_Shr t_U64 t_U128 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U128) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_125: Core.Ops.Bit.t_BitXor t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_bitxor_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_bitxor_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_bitxor
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_14__bitxor (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_126: Core.Ops.Bit.t_BitAnd t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_bitand_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_bitand_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_bitand
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_15__bitand (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_127: Core.Ops.Bit.t_BitOr t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_bitor_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_bitor_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_bitor
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_16__bitor (Core.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_132: Core.Ops.Arith.t_Neg t_U128 =
  {
    f_Output = t_U128;
    f_neg_pre = (fun (self: t_U128) -> true);
    f_neg_post = (fun (self: t_U128) (out: t_U128) -> true);
    f_neg
    =
    fun (self: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_7__sub Core.Base.Int.Base_spec.v_WORDSIZE_128_
            (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U128
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Int.t_HaxInt)
                Core.Base.Int.Base_spec.v_WORDSIZE_128_
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_138: Core.Ops.Arith.t_Mul t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_mul_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_mul_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_mul
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_11__mul (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_139: Core.Ops.Arith.t_Rem t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_rem_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_rem_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_rem
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__rem (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_140: Core.Ops.Arith.t_Add t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_add_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_add_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_add
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_141: Core.Ops.Arith.t_Div t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_div_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_div_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_div
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_10__div (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_142: Core.Ops.Bit.t_Shl t_U128 t_U8 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U8) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_143: Core.Ops.Bit.t_Shl t_U128 t_U16 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U16) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_144: Core.Ops.Bit.t_Shl t_U128 t_U32 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U32) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_145: Core.Ops.Bit.t_Shl t_U128 t_U64 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U64) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_146: Core.Ops.Bit.t_Shl t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_12__shl (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_147: Core.Ops.Bit.t_Shr t_U128 t_U8 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U8) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U8) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: Core.Base.Int.t_HaxInt
            )
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_148: Core.Ops.Bit.t_Shr t_U128 t_U16 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U16) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U16) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_149: Core.Ops.Bit.t_Shr t_U128 t_U32 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U32) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U32) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_150: Core.Ops.Bit.t_Shr t_U128 t_U64 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U64) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U64) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_151: Core.Ops.Bit.t_Shr t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_13__shr (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_152: Core.Ops.Bit.t_BitXor t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_bitxor_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_bitxor_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_bitxor
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_14__bitxor (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_153: Core.Ops.Bit.t_BitAnd t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_bitand_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_bitand_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_bitand
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_15__bitand (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_154: Core.Ops.Bit.t_BitOr t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_bitor_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_bitor_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_bitor
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Int.Base_impl.impl_16__bitor (Core.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Ops.Arith.t_Sub t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_sub_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_sub_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_sub
    =
    fun (self: t_U8) (rhs: t_U8) ->
      self +! (Core.Ops.Arith.f_neg #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Ops.Bit.t_Not t_U8 =
  {
    f_Output = t_U8;
    f_not_pre = (fun (self: t_U8) -> true);
    f_not_post = (fun (self: t_U8) (out: t_U8) -> true);
    f_not = fun (self: t_U8) -> self ^. (f_MAX <: t_U8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Ops.Arith.t_Sub t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_sub_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_sub_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_sub
    =
    fun (self: t_U16) (rhs: t_U16) ->
      self +! (Core.Ops.Arith.f_neg #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: Core.Ops.Bit.t_Not t_U16 =
  {
    f_Output = t_U16;
    f_not_pre = (fun (self: t_U16) -> true);
    f_not_post = (fun (self: t_U16) (out: t_U16) -> true);
    f_not = fun (self: t_U16) -> self ^. (f_MAX <: t_U16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_79: Core.Ops.Arith.t_Sub t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_sub_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_sub_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_sub
    =
    fun (self: t_U32) (rhs: t_U32) ->
      self +! (Core.Ops.Arith.f_neg #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_80: Core.Ops.Bit.t_Not t_U32 =
  {
    f_Output = t_U32;
    f_not_pre = (fun (self: t_U32) -> true);
    f_not_post = (fun (self: t_U32) (out: t_U32) -> true);
    f_not = fun (self: t_U32) -> self ^. (f_MAX <: t_U32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_106: Core.Ops.Arith.t_Sub t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_sub_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_sub_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_sub
    =
    fun (self: t_U64) (rhs: t_U64) ->
      self +! (Core.Ops.Arith.f_neg #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_107: Core.Ops.Bit.t_Not t_U64 =
  {
    f_Output = t_U64;
    f_not_pre = (fun (self: t_U64) -> true);
    f_not_post = (fun (self: t_U64) (out: t_U64) -> true);
    f_not = fun (self: t_U64) -> self ^. (f_MAX <: t_U64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_133: Core.Ops.Arith.t_Sub t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_sub_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_sub_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_sub
    =
    fun (self: t_U128) (rhs: t_U128) ->
      self +! (Core.Ops.Arith.f_neg #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_134: Core.Ops.Bit.t_Not t_U128 =
  {
    f_Output = t_U128;
    f_not_pre = (fun (self: t_U128) -> true);
    f_not_post = (fun (self: t_U128) (out: t_U128) -> true);
    f_not = fun (self: t_U128) -> self ^. (f_MAX <: t_U128)
  }
