module Core.Base.Int.Base_spec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let (~.) = not

let impl_9__ONE: Core.Base.Int.t_HaxInt = 1

let impl_9__ZERO: Core.Base.Int.t_HaxInt = 0

let v_BITS_128_: Core.Base.Int.t_HaxInt = 128

let v_BITS_16_: Core.Base.Int.t_HaxInt = 16

let v_BITS_32_: Core.Base.Int.t_HaxInt = 32

let v_BITS_64_: Core.Base.Int.t_HaxInt = 64

let v_BITS_8_: Core.Base.Int.t_HaxInt = 8

let v_WORDSIZE_128_: Core.Base.Int.t_HaxInt = pow2 128

let v_WORDSIZE_128_SUB_1_: Core.Base.Int.t_HaxInt = pow2 128 - 1

let v_WORDSIZE_16_: Core.Base.Int.t_HaxInt = pow2 16

let v_WORDSIZE_16_SUB_1_: Core.Base.Int.t_HaxInt = pow2 16 - 1

let v_WORDSIZE_32_: Core.Base.Int.t_HaxInt = pow2 32

let v_WORDSIZE_32_SUB_1_: Core.Base.Int.t_HaxInt = pow2 32 - 1

let v_WORDSIZE_64_: Core.Base.Int.t_HaxInt = pow2 64

let v_WORDSIZE_64_SUB_1_: Core.Base.Int.t_HaxInt = pow2 64 - 1

let v_WORDSIZE_8_: Core.Base.Int.t_HaxInt = pow2 8

let v_WORDSIZE_8_SUB_1_: Core.Base.Int.t_HaxInt = pow2 8 - 1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Clone.t_Clone Core.Base.Int.t_HaxInt =
  {
    f_clone_pre = (fun (self: Core.Base.Int.t_HaxInt) -> true);
    f_clone_post = (fun (self: Core.Base.Int.t_HaxInt) (out: Core.Base.Int.t_HaxInt) -> true);
    f_clone
    =
    fun (self: Core.Base.Int.t_HaxInt) -> self
  }

let impl_7__div2 (self: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt = self / 2

let impl_9__is_zero (self: Core.Base.Int.t_HaxInt) : bool = self = 0

let impl_9__pred (self: Core.Base.Int.t_HaxInt)
    : Prims.Pure Core.Base.Int.t_HaxInt
      (requires ~.(impl_9__is_zero self <: bool))
      (fun _ -> Prims.l_True) = self - 1

let impl_9__succ (self: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt = self + 1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Clone.t_Clone Core.Base.Int.t_Positive =
  {
    f_clone_pre = (fun (self: Core.Base.Int.t_Positive) -> true);
    f_clone_post = (fun (self: Core.Base.Int.t_Positive) (out: Core.Base.Int.t_Positive) -> true);
    f_clone
    =
    fun (self: Core.Base.Int.t_Positive) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Clone.t_Clone Core.Base.Int.t_Unary =
  {
    f_clone_pre = (fun (self: Core.Base.Int.t_Unary) -> true);
    f_clone_post = (fun (self: Core.Base.Int.t_Unary) (out: Core.Base.Int.t_Unary) -> true);
    f_clone
    =
    fun (self: Core.Base.Int.t_Unary) -> self
  }

let impl_4__from_int (x: Core.Base.Int.t_HaxInt{x > 0}) : Core.Base.Int.t_Positive = x

let impl_4__to_int (self: Core.Base.Int.t_Positive) : Core.Base.Int.t_HaxInt = self

let impl_5__from_int (x: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_Unary = x

let impl_5__to_int (self: Core.Base.Int.t_Unary) : Core.Base.Int.t_HaxInt = self

let impl_6__match_unary (self: Core.Base.Int.t_Unary) : Core.Base.Int.t_UNARY =
  if self = 0
  then Core.Base.Int.UNARY_ZERO
  else Core.Base.Int.UNARY_SUCC (self - 1)

let impl_8__is_xH (self: Core.Base.Int.t_Positive) : bool = self = 1

let impl_8__is_xI (self: Core.Base.Int.t_Positive) : bool = self > 1 && self % 2 = 1

let impl_8__is_xO (self: Core.Base.Int.t_Positive) : bool = self > 1 && self % 2 = 0

let impl_8__match_positive (self: Core.Base.Int.t_Positive) : Core.Base.Int.t_POSITIVE =
  if
    impl_8__is_xH (Core.Clone.f_clone #Core.Base.Int.t_Positive
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Base.Int.t_Positive)
  then Core.Base.Int.POSITIVE_XH <: Core.Base.Int.t_POSITIVE
  else
    if
      impl_8__is_xO (Core.Clone.f_clone #Core.Base.Int.t_Positive
            #FStar.Tactics.Typeclasses.solve
            self
          <:
          Core.Base.Int.t_Positive)
    then
      Core.Base.Int.POSITIVE_XO
      (impl_4__from_int (impl_7__div2 (impl_4__to_int self <: Core.Base.Int.t_HaxInt)
            <:
            Core.Base.Int.t_HaxInt))
      <:
      Core.Base.Int.t_POSITIVE
    else
      Core.Base.Int.POSITIVE_XI
      (impl_4__from_int (impl_7__div2 (impl_4__to_int self <: Core.Base.Int.t_HaxInt)
            <:
            Core.Base.Int.t_HaxInt))
      <:
      Core.Base.Int.t_POSITIVE

let impl_8__xH: Core.Base.Int.t_Positive = 1

let impl_8__xI (self: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive = self * 2 + 1

let impl_8__xO (self: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive = self * 2

let impl_9__match_pos (self: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_POS =
  if
    impl_9__is_zero (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Base.Int.t_HaxInt)
  then Core.Base.Int.POS_ZERO <: Core.Base.Int.t_POS
  else Core.Base.Int.POS_POS (impl_4__from_int self) <: Core.Base.Int.t_POS
