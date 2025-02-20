module Core.Base_interface.Int
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Constants (v_Self: Type0) = {
  f_ZERO:v_Self;
  f_ONE:v_Self;
  f_MIN:v_Self;
  f_MAX:v_Self
}

type t_I128 = { f_v:Core.Base.Spec.Z.t_Z }

type t_I16 = { f_v:Core.Base.Spec.Z.t_Z }

type t_I32 = { f_v:Core.Base.Spec.Z.t_Z }

type t_I64 = { f_v:Core.Base.Spec.Z.t_Z }

type t_I8 = { f_v:Core.Base.Spec.Z.t_Z }

type t_U128 = { f_v:Core.Base.Spec.Haxint.t_HaxInt }

type t_U16 = { f_v:Core.Base.Spec.Haxint.t_HaxInt }

type t_U32 = { f_v:Core.Base.Spec.Haxint.t_HaxInt }

type t_U64 = { f_v:Core.Base.Spec.Haxint.t_HaxInt }

type t_U8 = { f_v:Core.Base.Spec.Haxint.t_HaxInt }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I128 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I128) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: Core.Clone.t_Clone t_I128 =
  {
    f_clone_pre = (fun (self: t_I128) -> true);
    f_clone_post = (fun (self: t_I128) (out: t_I128) -> true);
    f_clone
    =
    fun (self: t_I128) ->
      { f_v = Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_I128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_70: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I64 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I64) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_91: Core.Clone.t_Clone t_I64 =
  {
    f_clone_pre = (fun (self: t_I64) -> true);
    f_clone_post = (fun (self: t_I64) (out: t_I64) -> true);
    f_clone
    =
    fun (self: t_I64) ->
      { f_v = Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_I64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_97: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I32 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I32) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_118: Core.Clone.t_Clone t_I32 =
  {
    f_clone_pre = (fun (self: t_I32) -> true);
    f_clone_post = (fun (self: t_I32) (out: t_I32) -> true);
    f_clone
    =
    fun (self: t_I32) ->
      { f_v = Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_I32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_124: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I16 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I16) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_145: Core.Clone.t_Clone t_I16 =
  {
    f_clone_pre = (fun (self: t_I16) -> true);
    f_clone_post = (fun (self: t_I16) (out: t_I16) -> true);
    f_clone
    =
    fun (self: t_I16) ->
      { f_v = Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_I16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_151: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I8 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I8) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_172: Core.Clone.t_Clone t_I8 =
  {
    f_clone_pre = (fun (self: t_I8) -> true);
    f_clone_post = (fun (self: t_I8) (out: t_I8) -> true);
    f_clone
    =
    fun (self: t_I8) ->
      { f_v = Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_I8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: t_Constants t_I128 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I128;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I128;
    f_MIN = { f_v = Core.Base.Spec.Constants.v_NEG_WORDSIZE_128_ } <: t_I128;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_POS_WORDSIZE_128_ } <: t_I128
  }

let impl_41__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_128_ } <: t_U32

let impl_41__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_128_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_67: t_Constants t_I64 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I64;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I64;
    f_MIN = { f_v = Core.Base.Spec.Constants.v_NEG_WORDSIZE_64_ } <: t_I64;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_POS_WORDSIZE_64_ } <: t_I64
  }

let impl_68__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_64_ } <: t_U32

let impl_68__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_64_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_94: t_Constants t_I32 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I32;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I32;
    f_MIN = { f_v = Core.Base.Spec.Constants.v_NEG_WORDSIZE_32_ } <: t_I32;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_POS_WORDSIZE_32_ } <: t_I32
  }

let impl_95__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_32_ } <: t_U32

let impl_95__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_32_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_121: t_Constants t_I16 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I16;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I16;
    f_MIN = { f_v = Core.Base.Spec.Constants.v_NEG_WORDSIZE_16_ } <: t_I16;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_POS_WORDSIZE_16_ } <: t_I16
  }

let impl_122__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_16_ } <: t_U32

let impl_122__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_16_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_148: t_Constants t_I8 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I8;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I8;
    f_MIN = { f_v = Core.Base.Spec.Constants.v_NEG_WORDSIZE_8_ } <: t_I8;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_POS_WORDSIZE_8_ } <: t_I8
  }

let impl_149__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_8_ } <: t_U32

let impl_149__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_8_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_175: t_Constants t_U128 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U128;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U128;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U128;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_128_SUB_1_ } <: t_U128
  }

let impl_176__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_128_ } <: t_U32

let impl_176__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_128_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_202: t_Constants t_U64 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U64;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U64;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U64;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_64_SUB_1_ } <: t_U64
  }

let impl_203__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_64_ } <: t_U32

let impl_203__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_64_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_229: t_Constants t_U32 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U32;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U32;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U32;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_32_SUB_1_ } <: t_U32
  }

let impl_230__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_32_ } <: t_U32

let impl_230__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_32_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_256: t_Constants t_U16 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U16;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U16;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U16;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_16_SUB_1_ } <: t_U16
  }

let impl_257__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_16_ } <: t_U32

let impl_257__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_16_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_283: t_Constants t_U8 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U8;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U8;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U8;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_8_SUB_1_ } <: t_U8
  }

let impl_284__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_8_ } <: t_U32

let impl_284__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_8_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_199: Core.Clone.t_Clone t_U128 =
  {
    f_clone_pre = (fun (self: t_U128) -> true);
    f_clone_post = (fun (self: t_U128) (out: t_U128) -> true);
    f_clone
    =
    fun (self: t_U128) ->
      {
        f_v
        =
        Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v
      }
      <:
      t_U128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_226: Core.Clone.t_Clone t_U64 =
  {
    f_clone_pre = (fun (self: t_U64) -> true);
    f_clone_post = (fun (self: t_U64) (out: t_U64) -> true);
    f_clone
    =
    fun (self: t_U64) ->
      {
        f_v
        =
        Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v
      }
      <:
      t_U64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_253: Core.Clone.t_Clone t_U32 =
  {
    f_clone_pre = (fun (self: t_U32) -> true);
    f_clone_post = (fun (self: t_U32) (out: t_U32) -> true);
    f_clone
    =
    fun (self: t_U32) ->
      {
        f_v
        =
        Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v
      }
      <:
      t_U32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_280: Core.Clone.t_Clone t_U16 =
  {
    f_clone_pre = (fun (self: t_U16) -> true);
    f_clone_post = (fun (self: t_U16) (out: t_U16) -> true);
    f_clone
    =
    fun (self: t_U16) ->
      {
        f_v
        =
        Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v
      }
      <:
      t_U16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_307: Core.Clone.t_Clone t_U8 =
  {
    f_clone_pre = (fun (self: t_U8) -> true);
    f_clone_post = (fun (self: t_U8) (out: t_U8) -> true);
    f_clone
    =
    fun (self: t_U8) ->
      {
        f_v
        =
        Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve self.f_v
      }
      <:
      t_U8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Base_interface.Coerce.t_Abstraction t_I128 =
  {
    f_AbstractType = Core.Base.Spec.Z.t_Z;
    f_lift_pre = (fun (self: t_I128) -> true);
    f_lift_post = (fun (self: t_I128) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_lift = fun (self: t_I128) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Convert.t_From t_I8 t_I128 =
  {
    f_from_pre = (fun (x: t_I128) -> true);
    f_from_post = (fun (x: t_I128) (out: t_I8) -> true);
    f_from
    =
    fun (x: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Convert.t_From t_I16 t_I128 =
  {
    f_from_pre = (fun (x: t_I128) -> true);
    f_from_post = (fun (x: t_I128) (out: t_I16) -> true);
    f_from
    =
    fun (x: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Convert.t_From t_I32 t_I128 =
  {
    f_from_pre = (fun (x: t_I128) -> true);
    f_from_post = (fun (x: t_I128) (out: t_I32) -> true);
    f_from
    =
    fun (x: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Convert.t_From t_I64 t_I128 =
  {
    f_from_pre = (fun (x: t_I128) -> true);
    f_from_post = (fun (x: t_I128) (out: t_I64) -> true);
    f_from
    =
    fun (x: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: Core.Cmp.t_PartialEq t_I128 t_I128 =
  {
    f_eq_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_eq_post = (fun (self: t_I128) (rhs: t_I128) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_I128) (rhs: t_I128) ->
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve self <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve rhs <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_ne_post = (fun (self: t_I128) (rhs: t_I128) (out: bool) -> true);
    f_ne
    =
    fun (self: t_I128) (rhs: t_I128) ->
      (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve self <: t_I128)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve rhs <: t_I128)
            <:
            Core.Base.Spec.Z.t_Z)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_66: Core.Cmp.t_PartialOrd t_I128 t_I128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_I128) (rhs: t_I128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_I128) (rhs: t_I128) ->
        Core.Option.Option_Some
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve self <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve rhs <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_lt_post = (fun (self: t_I128) (rhs: t_I128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_I128) (rhs: t_I128) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve self <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve rhs <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_le_post = (fun (self: t_I128) (rhs: t_I128) (out: bool) -> true);
    f_le
    =
    (fun (self: t_I128) (rhs: t_I128) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve self <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve rhs <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_gt_post = (fun (self: t_I128) (rhs: t_I128) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_I128) (rhs: t_I128) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve self <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve rhs <: t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_ge_post = (fun (self: t_I128) (rhs: t_I128) (out: bool) -> true);
    f_ge
    =
    fun (self: t_I128) (rhs: t_I128) ->
      match
        Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve self <: t_I128)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I128 #FStar.Tactics.Typeclasses.solve rhs <: t_I128)
            <:
            Core.Base.Spec.Z.t_Z)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_69: Core.Base_interface.Coerce.t_Abstraction t_I64 =
  {
    f_AbstractType = Core.Base.Spec.Z.t_Z;
    f_lift_pre = (fun (self: t_I64) -> true);
    f_lift_post = (fun (self: t_I64) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_lift = fun (self: t_I64) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Convert.t_From t_I8 t_I64 =
  {
    f_from_pre = (fun (x: t_I64) -> true);
    f_from_post = (fun (x: t_I64) (out: t_I8) -> true);
    f_from
    =
    fun (x: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Convert.t_From t_I16 t_I64 =
  {
    f_from_pre = (fun (x: t_I64) -> true);
    f_from_post = (fun (x: t_I64) (out: t_I16) -> true);
    f_from
    =
    fun (x: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Convert.t_From t_I32 t_I64 =
  {
    f_from_pre = (fun (x: t_I64) -> true);
    f_from_post = (fun (x: t_I64) (out: t_I32) -> true);
    f_from
    =
    fun (x: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Convert.t_From t_I128 t_I64 =
  {
    f_from_pre = (fun (x: t_I64) -> true);
    f_from_post = (fun (x: t_I64) (out: t_I128) -> true);
    f_from
    =
    fun (x: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_92: Core.Cmp.t_PartialEq t_I64 t_I64 =
  {
    f_eq_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_eq_post = (fun (self: t_I64) (rhs: t_I64) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_I64) (rhs: t_I64) ->
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve self <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve rhs <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_ne_post = (fun (self: t_I64) (rhs: t_I64) (out: bool) -> true);
    f_ne
    =
    fun (self: t_I64) (rhs: t_I64) ->
      (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve self <: t_I64)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve rhs <: t_I64)
            <:
            Core.Base.Spec.Z.t_Z)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_93: Core.Cmp.t_PartialOrd t_I64 t_I64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_I64) (rhs: t_I64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_I64) (rhs: t_I64) ->
        Core.Option.Option_Some
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve self <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve rhs <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_lt_post = (fun (self: t_I64) (rhs: t_I64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_I64) (rhs: t_I64) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve self <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve rhs <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_le_post = (fun (self: t_I64) (rhs: t_I64) (out: bool) -> true);
    f_le
    =
    (fun (self: t_I64) (rhs: t_I64) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve self <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve rhs <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_gt_post = (fun (self: t_I64) (rhs: t_I64) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_I64) (rhs: t_I64) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve self <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve rhs <: t_I64)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_ge_post = (fun (self: t_I64) (rhs: t_I64) (out: bool) -> true);
    f_ge
    =
    fun (self: t_I64) (rhs: t_I64) ->
      match
        Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve self <: t_I64)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I64 #FStar.Tactics.Typeclasses.solve rhs <: t_I64)
            <:
            Core.Base.Spec.Z.t_Z)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_96: Core.Base_interface.Coerce.t_Abstraction t_I32 =
  {
    f_AbstractType = Core.Base.Spec.Z.t_Z;
    f_lift_pre = (fun (self: t_I32) -> true);
    f_lift_post = (fun (self: t_I32) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_lift = fun (self: t_I32) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Convert.t_From t_I8 t_I32 =
  {
    f_from_pre = (fun (x: t_I32) -> true);
    f_from_post = (fun (x: t_I32) (out: t_I8) -> true);
    f_from
    =
    fun (x: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Convert.t_From t_I16 t_I32 =
  {
    f_from_pre = (fun (x: t_I32) -> true);
    f_from_post = (fun (x: t_I32) (out: t_I16) -> true);
    f_from
    =
    fun (x: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Convert.t_From t_I64 t_I32 =
  {
    f_from_pre = (fun (x: t_I32) -> true);
    f_from_post = (fun (x: t_I32) (out: t_I64) -> true);
    f_from
    =
    fun (x: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Convert.t_From t_I128 t_I32 =
  {
    f_from_pre = (fun (x: t_I32) -> true);
    f_from_post = (fun (x: t_I32) (out: t_I128) -> true);
    f_from
    =
    fun (x: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_119: Core.Cmp.t_PartialEq t_I32 t_I32 =
  {
    f_eq_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_eq_post = (fun (self: t_I32) (rhs: t_I32) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_I32) (rhs: t_I32) ->
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve self <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve rhs <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_ne_post = (fun (self: t_I32) (rhs: t_I32) (out: bool) -> true);
    f_ne
    =
    fun (self: t_I32) (rhs: t_I32) ->
      (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve self <: t_I32)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve rhs <: t_I32)
            <:
            Core.Base.Spec.Z.t_Z)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_120: Core.Cmp.t_PartialOrd t_I32 t_I32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_I32) (rhs: t_I32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_I32) (rhs: t_I32) ->
        Core.Option.Option_Some
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve self <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve rhs <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_lt_post = (fun (self: t_I32) (rhs: t_I32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_I32) (rhs: t_I32) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve self <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve rhs <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_le_post = (fun (self: t_I32) (rhs: t_I32) (out: bool) -> true);
    f_le
    =
    (fun (self: t_I32) (rhs: t_I32) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve self <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve rhs <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_gt_post = (fun (self: t_I32) (rhs: t_I32) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_I32) (rhs: t_I32) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve self <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve rhs <: t_I32)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_ge_post = (fun (self: t_I32) (rhs: t_I32) (out: bool) -> true);
    f_ge
    =
    fun (self: t_I32) (rhs: t_I32) ->
      match
        Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve self <: t_I32)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I32 #FStar.Tactics.Typeclasses.solve rhs <: t_I32)
            <:
            Core.Base.Spec.Z.t_Z)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_123: Core.Base_interface.Coerce.t_Abstraction t_I16 =
  {
    f_AbstractType = Core.Base.Spec.Z.t_Z;
    f_lift_pre = (fun (self: t_I16) -> true);
    f_lift_post = (fun (self: t_I16) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_lift = fun (self: t_I16) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Convert.t_From t_I8 t_I16 =
  {
    f_from_pre = (fun (x: t_I16) -> true);
    f_from_post = (fun (x: t_I16) (out: t_I8) -> true);
    f_from
    =
    fun (x: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Convert.t_From t_I32 t_I16 =
  {
    f_from_pre = (fun (x: t_I16) -> true);
    f_from_post = (fun (x: t_I16) (out: t_I32) -> true);
    f_from
    =
    fun (x: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Convert.t_From t_I64 t_I16 =
  {
    f_from_pre = (fun (x: t_I16) -> true);
    f_from_post = (fun (x: t_I16) (out: t_I64) -> true);
    f_from
    =
    fun (x: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Convert.t_From t_I128 t_I16 =
  {
    f_from_pre = (fun (x: t_I16) -> true);
    f_from_post = (fun (x: t_I16) (out: t_I128) -> true);
    f_from
    =
    fun (x: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_146: Core.Cmp.t_PartialEq t_I16 t_I16 =
  {
    f_eq_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_eq_post = (fun (self: t_I16) (rhs: t_I16) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_I16) (rhs: t_I16) ->
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve self <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve rhs <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_ne_post = (fun (self: t_I16) (rhs: t_I16) (out: bool) -> true);
    f_ne
    =
    fun (self: t_I16) (rhs: t_I16) ->
      (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve self <: t_I16)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve rhs <: t_I16)
            <:
            Core.Base.Spec.Z.t_Z)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_147: Core.Cmp.t_PartialOrd t_I16 t_I16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_I16) (rhs: t_I16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_I16) (rhs: t_I16) ->
        Core.Option.Option_Some
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve self <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve rhs <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_lt_post = (fun (self: t_I16) (rhs: t_I16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_I16) (rhs: t_I16) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve self <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve rhs <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_le_post = (fun (self: t_I16) (rhs: t_I16) (out: bool) -> true);
    f_le
    =
    (fun (self: t_I16) (rhs: t_I16) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve self <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve rhs <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_gt_post = (fun (self: t_I16) (rhs: t_I16) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_I16) (rhs: t_I16) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve self <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve rhs <: t_I16)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_ge_post = (fun (self: t_I16) (rhs: t_I16) (out: bool) -> true);
    f_ge
    =
    fun (self: t_I16) (rhs: t_I16) ->
      match
        Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve self <: t_I16)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I16 #FStar.Tactics.Typeclasses.solve rhs <: t_I16)
            <:
            Core.Base.Spec.Z.t_Z)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_150: Core.Base_interface.Coerce.t_Abstraction t_I8 =
  {
    f_AbstractType = Core.Base.Spec.Z.t_Z;
    f_lift_pre = (fun (self: t_I8) -> true);
    f_lift_post = (fun (self: t_I8) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_lift = fun (self: t_I8) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From t_I16 t_I8 =
  {
    f_from_pre = (fun (x: t_I8) -> true);
    f_from_post = (fun (x: t_I8) (out: t_I16) -> true);
    f_from
    =
    fun (x: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Convert.t_From t_I32 t_I8 =
  {
    f_from_pre = (fun (x: t_I8) -> true);
    f_from_post = (fun (x: t_I8) (out: t_I32) -> true);
    f_from
    =
    fun (x: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From t_I64 t_I8 =
  {
    f_from_pre = (fun (x: t_I8) -> true);
    f_from_post = (fun (x: t_I8) (out: t_I64) -> true);
    f_from
    =
    fun (x: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From t_I128 t_I8 =
  {
    f_from_pre = (fun (x: t_I8) -> true);
    f_from_post = (fun (x: t_I8) (out: t_I128) -> true);
    f_from
    =
    fun (x: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_173: Core.Cmp.t_PartialEq t_I8 t_I8 =
  {
    f_eq_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_eq_post = (fun (self: t_I8) (rhs: t_I8) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_I8) (rhs: t_I8) ->
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve self <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve rhs <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_ne_post = (fun (self: t_I8) (rhs: t_I8) (out: bool) -> true);
    f_ne
    =
    fun (self: t_I8) (rhs: t_I8) ->
      (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve self <: t_I8)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve rhs <: t_I8)
            <:
            Core.Base.Spec.Z.t_Z)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_174: Core.Cmp.t_PartialOrd t_I8 t_I8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_I8) (rhs: t_I8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_I8) (rhs: t_I8) ->
        Core.Option.Option_Some
        (Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve self <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve rhs <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_lt_post = (fun (self: t_I8) (rhs: t_I8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_I8) (rhs: t_I8) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve self <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve rhs <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_le_post = (fun (self: t_I8) (rhs: t_I8) (out: bool) -> true);
    f_le
    =
    (fun (self: t_I8) (rhs: t_I8) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve self <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve rhs <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_gt_post = (fun (self: t_I8) (rhs: t_I8) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_I8) (rhs: t_I8) ->
        match
          Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve self <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve rhs <: t_I8)
              <:
              Core.Base.Spec.Z.t_Z)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_ge_post = (fun (self: t_I8) (rhs: t_I8) (out: bool) -> true);
    f_ge
    =
    fun (self: t_I8) (rhs: t_I8) ->
      match
        Core.Base.Z.z_cmp (Core.Base_interface.Coerce.f_lift #t_I8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve self <: t_I8)
            <:
            Core.Base.Spec.Z.t_Z)
          (Core.Base_interface.Coerce.f_lift #t_I8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_I8 #FStar.Tactics.Typeclasses.solve rhs <: t_I8)
            <:
            Core.Base.Spec.Z.t_Z)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_177: Core.Base_interface.Coerce.t_Abstraction t_U128 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U128) -> true);
    f_lift_post = (fun (self: t_U128) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U128) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_200: Core.Cmp.t_PartialEq t_U128 t_U128 =
  {
    f_eq_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_eq_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_ne_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U128) (rhs: t_U128) ->
      (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_201: Core.Cmp.t_PartialOrd t_U128 t_U128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U128) (rhs: t_U128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        Core.Option.Option_Some
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_lt_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_le_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_gt_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U128) (rhs: t_U128) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_ge_post = (fun (self: t_U128) (rhs: t_U128) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U128) (rhs: t_U128) ->
      match
        Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve self <: t_U128)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U128
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U128 #FStar.Tactics.Typeclasses.solve rhs <: t_U128)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_204: Core.Base_interface.Coerce.t_Abstraction t_U64 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U64) -> true);
    f_lift_post = (fun (self: t_U64) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U64) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_227: Core.Cmp.t_PartialEq t_U64 t_U64 =
  {
    f_eq_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_eq_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_ne_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U64) (rhs: t_U64) ->
      (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_228: Core.Cmp.t_PartialOrd t_U64 t_U64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U64) (rhs: t_U64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        Core.Option.Option_Some
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_lt_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_le_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_gt_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U64) (rhs: t_U64) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_ge_post = (fun (self: t_U64) (rhs: t_U64) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U64) (rhs: t_U64) ->
      match
        Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve self <: t_U64)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U64
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U64 #FStar.Tactics.Typeclasses.solve rhs <: t_U64)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_231: Core.Base_interface.Coerce.t_Abstraction t_U32 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U32) -> true);
    f_lift_post = (fun (self: t_U32) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U32) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_254: Core.Cmp.t_PartialEq t_U32 t_U32 =
  {
    f_eq_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_eq_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_ne_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U32) (rhs: t_U32) ->
      (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_255: Core.Cmp.t_PartialOrd t_U32 t_U32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U32) (rhs: t_U32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        Core.Option.Option_Some
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_lt_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_le_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_gt_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U32) (rhs: t_U32) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_ge_post = (fun (self: t_U32) (rhs: t_U32) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U32) (rhs: t_U32) ->
      match
        Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve self <: t_U32)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U32
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U32 #FStar.Tactics.Typeclasses.solve rhs <: t_U32)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_258: Core.Base_interface.Coerce.t_Abstraction t_U16 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U16) -> true);
    f_lift_post = (fun (self: t_U16) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U16) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_281: Core.Cmp.t_PartialEq t_U16 t_U16 =
  {
    f_eq_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_eq_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_ne_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U16) (rhs: t_U16) ->
      (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_282: Core.Cmp.t_PartialOrd t_U16 t_U16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U16) (rhs: t_U16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        Core.Option.Option_Some
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_lt_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_le_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_gt_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U16) (rhs: t_U16) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_ge_post = (fun (self: t_U16) (rhs: t_U16) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U16) (rhs: t_U16) ->
      match
        Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve self <: t_U16)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U16
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U16 #FStar.Tactics.Typeclasses.solve rhs <: t_U16)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_285: Core.Base_interface.Coerce.t_Abstraction t_U8 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U8) -> true);
    f_lift_post = (fun (self: t_U8) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U8) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_308: Core.Cmp.t_PartialEq t_U8 t_U8 =
  {
    f_eq_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_eq_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering));
    f_ne_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_ne_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_ne
    =
    fun (self: t_U8) (rhs: t_U8) ->
      (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
        <:
        Core.Cmp.t_Ordering) <>.
      (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_309: Core.Cmp.t_PartialOrd t_U8 t_U8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_U8) (rhs: t_U8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        Core.Option.Option_Some
        (Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_lt_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  -> true
        | _ -> false);
    f_le_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_le_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_le
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Less  | Core.Cmp.Ordering_Equal  -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_gt_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_U8) (rhs: t_U8) ->
        match
          Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
        with
        | Core.Cmp.Ordering_Greater  -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_ge_post = (fun (self: t_U8) (rhs: t_U8) (out: bool) -> true);
    f_ge
    =
    fun (self: t_U8) (rhs: t_U8) ->
      match
        Core.Base.Pos.haxint_cmp (Core.Base_interface.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve self <: t_U8)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
          (Core.Base_interface.Coerce.f_lift #t_U8
              #FStar.Tactics.Typeclasses.solve
              (Core.Clone.f_clone #t_U8 #FStar.Tactics.Typeclasses.solve rhs <: t_U8)
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
      with
      | Core.Cmp.Ordering_Greater  | Core.Cmp.Ordering_Equal  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Ops.Arith.t_Neg t_I128 =
  {
    f_Output = t_I128;
    f_neg_pre = (fun (self: t_I128) -> true);
    f_neg_post = (fun (self: t_I128) (out: t_I128) -> true);
    f_neg
    =
    fun (self: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Ops.Bit.t_Shl t_I128 t_I8 =
  {
    f_Output = t_I128;
    f_shl_pre = (fun (self: t_I128) (rhs: t_I8) -> true);
    f_shl_post = (fun (self: t_I128) (rhs: t_I8) (out: t_I128) -> true);
    f_shl
    =
    fun (self: t_I128) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Ops.Bit.t_Shl t_I128 t_I16 =
  {
    f_Output = t_I128;
    f_shl_pre = (fun (self: t_I128) (rhs: t_I16) -> true);
    f_shl_post = (fun (self: t_I128) (rhs: t_I16) (out: t_I128) -> true);
    f_shl
    =
    fun (self: t_I128) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: Core.Ops.Bit.t_Shl t_I128 t_I32 =
  {
    f_Output = t_I128;
    f_shl_pre = (fun (self: t_I128) (rhs: t_I32) -> true);
    f_shl_post = (fun (self: t_I128) (rhs: t_I32) (out: t_I128) -> true);
    f_shl
    =
    fun (self: t_I128) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: Core.Ops.Bit.t_Shl t_I128 t_I64 =
  {
    f_Output = t_I128;
    f_shl_pre = (fun (self: t_I128) (rhs: t_I64) -> true);
    f_shl_post = (fun (self: t_I128) (rhs: t_I64) (out: t_I128) -> true);
    f_shl
    =
    fun (self: t_I128) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: Core.Ops.Bit.t_Shl t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_shl_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_shl_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_shl
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: Core.Ops.Bit.t_Shr t_I128 t_I8 =
  {
    f_Output = t_I128;
    f_shr_pre = (fun (self: t_I128) (rhs: t_I8) -> true);
    f_shr_post = (fun (self: t_I128) (rhs: t_I8) (out: t_I128) -> true);
    f_shr
    =
    fun (self: t_I128) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: Core.Ops.Bit.t_Shr t_I128 t_I16 =
  {
    f_Output = t_I128;
    f_shr_pre = (fun (self: t_I128) (rhs: t_I16) -> true);
    f_shr_post = (fun (self: t_I128) (rhs: t_I16) (out: t_I128) -> true);
    f_shr
    =
    fun (self: t_I128) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: Core.Ops.Bit.t_Shr t_I128 t_I32 =
  {
    f_Output = t_I128;
    f_shr_pre = (fun (self: t_I128) (rhs: t_I32) -> true);
    f_shr_post = (fun (self: t_I128) (rhs: t_I32) (out: t_I128) -> true);
    f_shr
    =
    fun (self: t_I128) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: Core.Ops.Bit.t_Shr t_I128 t_I64 =
  {
    f_Output = t_I128;
    f_shr_pre = (fun (self: t_I128) (rhs: t_I64) -> true);
    f_shr_post = (fun (self: t_I128) (rhs: t_I64) (out: t_I128) -> true);
    f_shr
    =
    fun (self: t_I128) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: Core.Ops.Bit.t_Shr t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_shr_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_shr_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_shr
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: Core.Ops.Bit.t_BitXor t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_bitxor_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_bitxor_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_bitxor
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitxor (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: Core.Ops.Bit.t_BitAnd t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_bitand_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_bitand_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_bitand
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitand (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: Core.Ops.Bit.t_BitOr t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_bitor_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_bitor_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_bitor
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitor (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_76: Core.Ops.Arith.t_Neg t_I64 =
  {
    f_Output = t_I64;
    f_neg_pre = (fun (self: t_I64) -> true);
    f_neg_post = (fun (self: t_I64) (out: t_I64) -> true);
    f_neg
    =
    fun (self: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_78: Core.Ops.Bit.t_Shl t_I64 t_I8 =
  {
    f_Output = t_I64;
    f_shl_pre = (fun (self: t_I64) (rhs: t_I8) -> true);
    f_shl_post = (fun (self: t_I64) (rhs: t_I8) (out: t_I64) -> true);
    f_shl
    =
    fun (self: t_I64) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_79: Core.Ops.Bit.t_Shl t_I64 t_I16 =
  {
    f_Output = t_I64;
    f_shl_pre = (fun (self: t_I64) (rhs: t_I16) -> true);
    f_shl_post = (fun (self: t_I64) (rhs: t_I16) (out: t_I64) -> true);
    f_shl
    =
    fun (self: t_I64) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_80: Core.Ops.Bit.t_Shl t_I64 t_I32 =
  {
    f_Output = t_I64;
    f_shl_pre = (fun (self: t_I64) (rhs: t_I32) -> true);
    f_shl_post = (fun (self: t_I64) (rhs: t_I32) (out: t_I64) -> true);
    f_shl
    =
    fun (self: t_I64) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_81: Core.Ops.Bit.t_Shl t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_shl_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_shl_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_shl
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_82: Core.Ops.Bit.t_Shl t_I64 t_I128 =
  {
    f_Output = t_I64;
    f_shl_pre = (fun (self: t_I64) (rhs: t_I128) -> true);
    f_shl_post = (fun (self: t_I64) (rhs: t_I128) (out: t_I64) -> true);
    f_shl
    =
    fun (self: t_I64) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_83: Core.Ops.Bit.t_Shr t_I64 t_I8 =
  {
    f_Output = t_I64;
    f_shr_pre = (fun (self: t_I64) (rhs: t_I8) -> true);
    f_shr_post = (fun (self: t_I64) (rhs: t_I8) (out: t_I64) -> true);
    f_shr
    =
    fun (self: t_I64) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_84: Core.Ops.Bit.t_Shr t_I64 t_I16 =
  {
    f_Output = t_I64;
    f_shr_pre = (fun (self: t_I64) (rhs: t_I16) -> true);
    f_shr_post = (fun (self: t_I64) (rhs: t_I16) (out: t_I64) -> true);
    f_shr
    =
    fun (self: t_I64) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_85: Core.Ops.Bit.t_Shr t_I64 t_I32 =
  {
    f_Output = t_I64;
    f_shr_pre = (fun (self: t_I64) (rhs: t_I32) -> true);
    f_shr_post = (fun (self: t_I64) (rhs: t_I32) (out: t_I64) -> true);
    f_shr
    =
    fun (self: t_I64) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_86: Core.Ops.Bit.t_Shr t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_shr_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_shr_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_shr
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_87: Core.Ops.Bit.t_Shr t_I64 t_I128 =
  {
    f_Output = t_I64;
    f_shr_pre = (fun (self: t_I64) (rhs: t_I128) -> true);
    f_shr_post = (fun (self: t_I64) (rhs: t_I128) (out: t_I64) -> true);
    f_shr
    =
    fun (self: t_I64) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_88: Core.Ops.Bit.t_BitXor t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_bitxor_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_bitxor_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_bitxor
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitxor (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_89: Core.Ops.Bit.t_BitAnd t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_bitand_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_bitand_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_bitand
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitand (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_90: Core.Ops.Bit.t_BitOr t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_bitor_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_bitor_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_bitor
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitor (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_103: Core.Ops.Arith.t_Neg t_I32 =
  {
    f_Output = t_I32;
    f_neg_pre = (fun (self: t_I32) -> true);
    f_neg_post = (fun (self: t_I32) (out: t_I32) -> true);
    f_neg
    =
    fun (self: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_105: Core.Ops.Bit.t_Shl t_I32 t_I8 =
  {
    f_Output = t_I32;
    f_shl_pre = (fun (self: t_I32) (rhs: t_I8) -> true);
    f_shl_post = (fun (self: t_I32) (rhs: t_I8) (out: t_I32) -> true);
    f_shl
    =
    fun (self: t_I32) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_106: Core.Ops.Bit.t_Shl t_I32 t_I16 =
  {
    f_Output = t_I32;
    f_shl_pre = (fun (self: t_I32) (rhs: t_I16) -> true);
    f_shl_post = (fun (self: t_I32) (rhs: t_I16) (out: t_I32) -> true);
    f_shl
    =
    fun (self: t_I32) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_107: Core.Ops.Bit.t_Shl t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_shl_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_shl_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_shl
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_108: Core.Ops.Bit.t_Shl t_I32 t_I64 =
  {
    f_Output = t_I32;
    f_shl_pre = (fun (self: t_I32) (rhs: t_I64) -> true);
    f_shl_post = (fun (self: t_I32) (rhs: t_I64) (out: t_I32) -> true);
    f_shl
    =
    fun (self: t_I32) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_109: Core.Ops.Bit.t_Shl t_I32 t_I128 =
  {
    f_Output = t_I32;
    f_shl_pre = (fun (self: t_I32) (rhs: t_I128) -> true);
    f_shl_post = (fun (self: t_I32) (rhs: t_I128) (out: t_I32) -> true);
    f_shl
    =
    fun (self: t_I32) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_110: Core.Ops.Bit.t_Shr t_I32 t_I8 =
  {
    f_Output = t_I32;
    f_shr_pre = (fun (self: t_I32) (rhs: t_I8) -> true);
    f_shr_post = (fun (self: t_I32) (rhs: t_I8) (out: t_I32) -> true);
    f_shr
    =
    fun (self: t_I32) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_111: Core.Ops.Bit.t_Shr t_I32 t_I16 =
  {
    f_Output = t_I32;
    f_shr_pre = (fun (self: t_I32) (rhs: t_I16) -> true);
    f_shr_post = (fun (self: t_I32) (rhs: t_I16) (out: t_I32) -> true);
    f_shr
    =
    fun (self: t_I32) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_112: Core.Ops.Bit.t_Shr t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_shr_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_shr_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_shr
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_113: Core.Ops.Bit.t_Shr t_I32 t_I64 =
  {
    f_Output = t_I32;
    f_shr_pre = (fun (self: t_I32) (rhs: t_I64) -> true);
    f_shr_post = (fun (self: t_I32) (rhs: t_I64) (out: t_I32) -> true);
    f_shr
    =
    fun (self: t_I32) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_114: Core.Ops.Bit.t_Shr t_I32 t_I128 =
  {
    f_Output = t_I32;
    f_shr_pre = (fun (self: t_I32) (rhs: t_I128) -> true);
    f_shr_post = (fun (self: t_I32) (rhs: t_I128) (out: t_I32) -> true);
    f_shr
    =
    fun (self: t_I32) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_115: Core.Ops.Bit.t_BitXor t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_bitxor_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_bitxor_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_bitxor
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitxor (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_116: Core.Ops.Bit.t_BitAnd t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_bitand_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_bitand_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_bitand
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitand (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_117: Core.Ops.Bit.t_BitOr t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_bitor_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_bitor_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_bitor
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitor (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_130: Core.Ops.Arith.t_Neg t_I16 =
  {
    f_Output = t_I16;
    f_neg_pre = (fun (self: t_I16) -> true);
    f_neg_post = (fun (self: t_I16) (out: t_I16) -> true);
    f_neg
    =
    fun (self: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_132: Core.Ops.Bit.t_Shl t_I16 t_I8 =
  {
    f_Output = t_I16;
    f_shl_pre = (fun (self: t_I16) (rhs: t_I8) -> true);
    f_shl_post = (fun (self: t_I16) (rhs: t_I8) (out: t_I16) -> true);
    f_shl
    =
    fun (self: t_I16) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_133: Core.Ops.Bit.t_Shl t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_shl_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_shl_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_shl
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_134: Core.Ops.Bit.t_Shl t_I16 t_I32 =
  {
    f_Output = t_I16;
    f_shl_pre = (fun (self: t_I16) (rhs: t_I32) -> true);
    f_shl_post = (fun (self: t_I16) (rhs: t_I32) (out: t_I16) -> true);
    f_shl
    =
    fun (self: t_I16) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_135: Core.Ops.Bit.t_Shl t_I16 t_I64 =
  {
    f_Output = t_I16;
    f_shl_pre = (fun (self: t_I16) (rhs: t_I64) -> true);
    f_shl_post = (fun (self: t_I16) (rhs: t_I64) (out: t_I16) -> true);
    f_shl
    =
    fun (self: t_I16) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_136: Core.Ops.Bit.t_Shl t_I16 t_I128 =
  {
    f_Output = t_I16;
    f_shl_pre = (fun (self: t_I16) (rhs: t_I128) -> true);
    f_shl_post = (fun (self: t_I16) (rhs: t_I128) (out: t_I16) -> true);
    f_shl
    =
    fun (self: t_I16) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_137: Core.Ops.Bit.t_Shr t_I16 t_I8 =
  {
    f_Output = t_I16;
    f_shr_pre = (fun (self: t_I16) (rhs: t_I8) -> true);
    f_shr_post = (fun (self: t_I16) (rhs: t_I8) (out: t_I16) -> true);
    f_shr
    =
    fun (self: t_I16) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_138: Core.Ops.Bit.t_Shr t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_shr_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_shr_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_shr
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_139: Core.Ops.Bit.t_Shr t_I16 t_I32 =
  {
    f_Output = t_I16;
    f_shr_pre = (fun (self: t_I16) (rhs: t_I32) -> true);
    f_shr_post = (fun (self: t_I16) (rhs: t_I32) (out: t_I16) -> true);
    f_shr
    =
    fun (self: t_I16) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_140: Core.Ops.Bit.t_Shr t_I16 t_I64 =
  {
    f_Output = t_I16;
    f_shr_pre = (fun (self: t_I16) (rhs: t_I64) -> true);
    f_shr_post = (fun (self: t_I16) (rhs: t_I64) (out: t_I16) -> true);
    f_shr
    =
    fun (self: t_I16) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_141: Core.Ops.Bit.t_Shr t_I16 t_I128 =
  {
    f_Output = t_I16;
    f_shr_pre = (fun (self: t_I16) (rhs: t_I128) -> true);
    f_shr_post = (fun (self: t_I16) (rhs: t_I128) (out: t_I16) -> true);
    f_shr
    =
    fun (self: t_I16) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_142: Core.Ops.Bit.t_BitXor t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_bitxor_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_bitxor_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_bitxor
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitxor (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_143: Core.Ops.Bit.t_BitAnd t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_bitand_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_bitand_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_bitand
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitand (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_144: Core.Ops.Bit.t_BitOr t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_bitor_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_bitor_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_bitor
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitor (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_157: Core.Ops.Arith.t_Neg t_I8 =
  {
    f_Output = t_I8;
    f_neg_pre = (fun (self: t_I8) -> true);
    f_neg_post = (fun (self: t_I8) (out: t_I8) -> true);
    f_neg
    =
    fun (self: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_159: Core.Ops.Bit.t_Shl t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_shl_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_shl_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_shl
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_160: Core.Ops.Bit.t_Shl t_I8 t_I16 =
  {
    f_Output = t_I8;
    f_shl_pre = (fun (self: t_I8) (rhs: t_I16) -> true);
    f_shl_post = (fun (self: t_I8) (rhs: t_I16) (out: t_I8) -> true);
    f_shl
    =
    fun (self: t_I8) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_161: Core.Ops.Bit.t_Shl t_I8 t_I32 =
  {
    f_Output = t_I8;
    f_shl_pre = (fun (self: t_I8) (rhs: t_I32) -> true);
    f_shl_post = (fun (self: t_I8) (rhs: t_I32) (out: t_I8) -> true);
    f_shl
    =
    fun (self: t_I8) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_162: Core.Ops.Bit.t_Shl t_I8 t_I64 =
  {
    f_Output = t_I8;
    f_shl_pre = (fun (self: t_I8) (rhs: t_I64) -> true);
    f_shl_post = (fun (self: t_I8) (rhs: t_I64) (out: t_I8) -> true);
    f_shl
    =
    fun (self: t_I8) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_163: Core.Ops.Bit.t_Shl t_I8 t_I128 =
  {
    f_Output = t_I8;
    f_shl_pre = (fun (self: t_I8) (rhs: t_I128) -> true);
    f_shl_post = (fun (self: t_I8) (rhs: t_I128) (out: t_I8) -> true);
    f_shl
    =
    fun (self: t_I8) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shl (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_164: Core.Ops.Bit.t_Shr t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_shr_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_shr_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_shr
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_165: Core.Ops.Bit.t_Shr t_I8 t_I16 =
  {
    f_Output = t_I8;
    f_shr_pre = (fun (self: t_I8) (rhs: t_I16) -> true);
    f_shr_post = (fun (self: t_I8) (rhs: t_I16) (out: t_I8) -> true);
    f_shr
    =
    fun (self: t_I8) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_166: Core.Ops.Bit.t_Shr t_I8 t_I32 =
  {
    f_Output = t_I8;
    f_shr_pre = (fun (self: t_I8) (rhs: t_I32) -> true);
    f_shr_post = (fun (self: t_I8) (rhs: t_I32) (out: t_I8) -> true);
    f_shr
    =
    fun (self: t_I8) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_167: Core.Ops.Bit.t_Shr t_I8 t_I64 =
  {
    f_Output = t_I8;
    f_shr_pre = (fun (self: t_I8) (rhs: t_I64) -> true);
    f_shr_post = (fun (self: t_I8) (rhs: t_I64) (out: t_I8) -> true);
    f_shr
    =
    fun (self: t_I8) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_168: Core.Ops.Bit.t_Shr t_I8 t_I128 =
  {
    f_Output = t_I8;
    f_shr_pre = (fun (self: t_I8) (rhs: t_I128) -> true);
    f_shr_post = (fun (self: t_I8) (rhs: t_I128) (out: t_I8) -> true);
    f_shr
    =
    fun (self: t_I8) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_shr (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_169: Core.Ops.Bit.t_BitXor t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_bitxor_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_bitxor_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_bitxor
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitxor (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_170: Core.Ops.Bit.t_BitAnd t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_bitand_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_bitand_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_bitand
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitand (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_171: Core.Ops.Bit.t_BitOr t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_bitor_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_bitor_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_bitor
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_bitor (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Ops.Bit.t_Not t_I128 =
  {
    f_Output = t_I128;
    f_not_pre = (fun (self: t_I128) -> true);
    f_not_post = (fun (self: t_I128) (out: t_I128) -> true);
    f_not
    =
    fun (self: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I128
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Z.t_Z)
              <:
              Core.Base.Spec.Z.t_Z)
            Core.Base.Spec.Z.v_Z_ONE
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: Core.Ops.Arith.t_Add t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_add_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_add_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_add
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Ops.Arith.t_Sub t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_sub_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_sub_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_sub
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_71: Core.Ops.Bit.t_Not t_I64 =
  {
    f_Output = t_I64;
    f_not_pre = (fun (self: t_I64) -> true);
    f_not_post = (fun (self: t_I64) (out: t_I64) -> true);
    f_not
    =
    fun (self: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I64
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Z.t_Z)
              <:
              Core.Base.Spec.Z.t_Z)
            Core.Base.Spec.Z.v_Z_ONE
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_74: Core.Ops.Arith.t_Add t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_add_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_add_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_add
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_77: Core.Ops.Arith.t_Sub t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_sub_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_sub_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_sub
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_98: Core.Ops.Bit.t_Not t_I32 =
  {
    f_Output = t_I32;
    f_not_pre = (fun (self: t_I32) -> true);
    f_not_post = (fun (self: t_I32) (out: t_I32) -> true);
    f_not
    =
    fun (self: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I32
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Z.t_Z)
              <:
              Core.Base.Spec.Z.t_Z)
            Core.Base.Spec.Z.v_Z_ONE
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_101: Core.Ops.Arith.t_Add t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_add_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_add_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_add
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_104: Core.Ops.Arith.t_Sub t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_sub_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_sub_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_sub
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_125: Core.Ops.Bit.t_Not t_I16 =
  {
    f_Output = t_I16;
    f_not_pre = (fun (self: t_I16) -> true);
    f_not_post = (fun (self: t_I16) (out: t_I16) -> true);
    f_not
    =
    fun (self: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I16
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Z.t_Z)
              <:
              Core.Base.Spec.Z.t_Z)
            Core.Base.Spec.Z.v_Z_ONE
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_128: Core.Ops.Arith.t_Add t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_add_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_add_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_add
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_131: Core.Ops.Arith.t_Sub t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_sub_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_sub_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_sub
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_152: Core.Ops.Bit.t_Not t_I8 =
  {
    f_Output = t_I8;
    f_not_pre = (fun (self: t_I8) -> true);
    f_not_post = (fun (self: t_I8) (out: t_I8) -> true);
    f_not
    =
    fun (self: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base.Z.z_neg (Core.Base_interface.Coerce.f_lift #t_I8
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Z.t_Z)
              <:
              Core.Base.Spec.Z.t_Z)
            Core.Base.Spec.Z.v_Z_ONE
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_155: Core.Ops.Arith.t_Add t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_add_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_add_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_add
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_158: Core.Ops.Arith.t_Sub t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_sub_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_sub_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_sub
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_sub (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_178: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U128 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) (out: t_U128) -> true);
    f_concretize
    =
    fun (self: Core.Base.Spec.Haxint.t_HaxInt) ->
      { f_v = Core.Base.Pos.haxint_rem self Core.Base.Spec.Constants.v_WORDSIZE_128_ } <: t_U128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From t_U128 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From t_U128 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From t_U128 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From t_U128 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U128) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_205: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U64 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) (out: t_U64) -> true);
    f_concretize
    =
    fun (self: Core.Base.Spec.Haxint.t_HaxInt) ->
      { f_v = Core.Base.Pos.haxint_rem self Core.Base.Spec.Constants.v_WORDSIZE_64_ } <: t_U64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From t_U64 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From t_U64 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From t_U64 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From t_U64 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U64) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_232: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U32 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) (out: t_U32) -> true);
    f_concretize
    =
    fun (self: Core.Base.Spec.Haxint.t_HaxInt) ->
      { f_v = Core.Base.Pos.haxint_rem self Core.Base.Spec.Constants.v_WORDSIZE_32_ } <: t_U32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_U32 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From t_U32 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From t_U32 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From t_U32 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U32) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_259: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U16 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) (out: t_U16) -> true);
    f_concretize
    =
    fun (self: Core.Base.Spec.Haxint.t_HaxInt) ->
      { f_v = Core.Base.Pos.haxint_rem self Core.Base.Spec.Constants.v_WORDSIZE_16_ } <: t_U16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_U16 t_U8 =
  {
    f_from_pre = (fun (x: t_U8) -> true);
    f_from_post = (fun (x: t_U8) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From t_U16 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From t_U16 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From t_U16 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U16) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_286: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U8 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Haxint.t_HaxInt) (out: t_U8) -> true);
    f_concretize
    =
    fun (self: Core.Base.Spec.Haxint.t_HaxInt) ->
      { f_v = Core.Base.Pos.haxint_rem self Core.Base.Spec.Constants.v_WORDSIZE_8_ } <: t_U8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From t_U8 t_U16 =
  {
    f_from_pre = (fun (x: t_U16) -> true);
    f_from_post = (fun (x: t_U16) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From t_U8 t_U32 =
  {
    f_from_pre = (fun (x: t_U32) -> true);
    f_from_post = (fun (x: t_U32) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From t_U8 t_U64 =
  {
    f_from_pre = (fun (x: t_U64) -> true);
    f_from_post = (fun (x: t_U64) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From t_U8 t_U128 =
  {
    f_from_pre = (fun (x: t_U128) -> true);
    f_from_post = (fun (x: t_U128) (out: t_U8) -> true);
    f_from
    =
    fun (x: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve x
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Ops.Arith.t_Mul t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_mul_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_mul_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_mul
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_mul (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_72: Core.Ops.Arith.t_Mul t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_mul_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_mul_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_mul
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_mul (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_99: Core.Ops.Arith.t_Mul t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_mul_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_mul_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_mul
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_mul (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_126: Core.Ops.Arith.t_Mul t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_mul_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_mul_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_mul
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_mul (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_153: Core.Ops.Arith.t_Mul t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_mul_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_mul_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_mul
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_mul (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_179: Core.Ops.Arith.t_Neg t_U128 =
  {
    f_Output = t_U128;
    f_neg_pre = (fun (self: t_U128) -> true);
    f_neg_post = (fun (self: t_U128) (out: t_U128) -> true);
    f_neg
    =
    fun (self: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_sub Core.Base.Spec.Constants.v_WORDSIZE_128_
            (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U128
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Haxint.t_HaxInt)
                Core.Base.Spec.Constants.v_WORDSIZE_128_
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_182: Core.Ops.Arith.t_Mul t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_mul_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_mul_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_mul
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_mul (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_183: Core.Ops.Arith.t_Rem t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_rem_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_rem_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_rem
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_184: Core.Ops.Arith.t_Add t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_add_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_add_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_add
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_185: Core.Ops.Arith.t_Div t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_div_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_div_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_div
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_186: Core.Ops.Bit.t_Shl t_U128 t_U8 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U8) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_187: Core.Ops.Bit.t_Shl t_U128 t_U16 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U16) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_188: Core.Ops.Bit.t_Shl t_U128 t_U32 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U32) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_189: Core.Ops.Bit.t_Shl t_U128 t_U64 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U64) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_190: Core.Ops.Bit.t_Shl t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_shl_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_shl
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_191: Core.Ops.Bit.t_Shr t_U128 t_U8 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U8) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_192: Core.Ops.Bit.t_Shr t_U128 t_U16 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U16) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_193: Core.Ops.Bit.t_Shr t_U128 t_U32 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U32) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_194: Core.Ops.Bit.t_Shr t_U128 t_U64 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U64) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_195: Core.Ops.Bit.t_Shr t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_shr_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_shr
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_196: Core.Ops.Bit.t_BitXor t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_bitxor_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_bitxor_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_bitxor
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitxor (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_197: Core.Ops.Bit.t_BitAnd t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_bitand_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_bitand_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_bitand
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitand (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_198: Core.Ops.Bit.t_BitOr t_U128 t_U128 =
  {
    f_Output = t_U128;
    f_bitor_pre = (fun (self: t_U128) (rhs: t_U128) -> true);
    f_bitor_post = (fun (self: t_U128) (rhs: t_U128) (out: t_U128) -> true);
    f_bitor
    =
    fun (self: t_U128) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitor (Core.Base_interface.Coerce.f_lift #t_U128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_206: Core.Ops.Arith.t_Neg t_U64 =
  {
    f_Output = t_U64;
    f_neg_pre = (fun (self: t_U64) -> true);
    f_neg_post = (fun (self: t_U64) (out: t_U64) -> true);
    f_neg
    =
    fun (self: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_sub Core.Base.Spec.Constants.v_WORDSIZE_64_
            (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U64
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Haxint.t_HaxInt)
                Core.Base.Spec.Constants.v_WORDSIZE_64_
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_209: Core.Ops.Arith.t_Mul t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_mul_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_mul_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_mul
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_mul (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_210: Core.Ops.Arith.t_Rem t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_rem_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_rem_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_rem
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_211: Core.Ops.Arith.t_Add t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_add_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_add_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_add
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_212: Core.Ops.Arith.t_Div t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_div_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_div_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_div
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_213: Core.Ops.Bit.t_Shl t_U64 t_U8 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U8) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_214: Core.Ops.Bit.t_Shl t_U64 t_U16 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U16) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_215: Core.Ops.Bit.t_Shl t_U64 t_U32 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U32) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_216: Core.Ops.Bit.t_Shl t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_217: Core.Ops.Bit.t_Shl t_U64 t_U128 =
  {
    f_Output = t_U64;
    f_shl_pre = (fun (self: t_U64) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U64) (rhs: t_U128) (out: t_U64) -> true);
    f_shl
    =
    fun (self: t_U64) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_218: Core.Ops.Bit.t_Shr t_U64 t_U8 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U8) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_219: Core.Ops.Bit.t_Shr t_U64 t_U16 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U16) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_220: Core.Ops.Bit.t_Shr t_U64 t_U32 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U32) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_221: Core.Ops.Bit.t_Shr t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_222: Core.Ops.Bit.t_Shr t_U64 t_U128 =
  {
    f_Output = t_U64;
    f_shr_pre = (fun (self: t_U64) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U64) (rhs: t_U128) (out: t_U64) -> true);
    f_shr
    =
    fun (self: t_U64) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_223: Core.Ops.Bit.t_BitXor t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_bitxor_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_bitxor_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_bitxor
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitxor (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_224: Core.Ops.Bit.t_BitAnd t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_bitand_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_bitand_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_bitand
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitand (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_225: Core.Ops.Bit.t_BitOr t_U64 t_U64 =
  {
    f_Output = t_U64;
    f_bitor_pre = (fun (self: t_U64) (rhs: t_U64) -> true);
    f_bitor_post = (fun (self: t_U64) (rhs: t_U64) (out: t_U64) -> true);
    f_bitor
    =
    fun (self: t_U64) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitor (Core.Base_interface.Coerce.f_lift #t_U64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_233: Core.Ops.Arith.t_Neg t_U32 =
  {
    f_Output = t_U32;
    f_neg_pre = (fun (self: t_U32) -> true);
    f_neg_post = (fun (self: t_U32) (out: t_U32) -> true);
    f_neg
    =
    fun (self: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_sub Core.Base.Spec.Constants.v_WORDSIZE_32_
            (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U32
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Haxint.t_HaxInt)
                Core.Base.Spec.Constants.v_WORDSIZE_32_
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_236: Core.Ops.Arith.t_Mul t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_mul_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_mul_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_mul
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_mul (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_237: Core.Ops.Arith.t_Rem t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_rem_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_rem_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_rem
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_238: Core.Ops.Arith.t_Add t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_add_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_add_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_add
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_239: Core.Ops.Arith.t_Div t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_div_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_div_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_div
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_240: Core.Ops.Bit.t_Shl t_U32 t_U8 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U8) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_241: Core.Ops.Bit.t_Shl t_U32 t_U16 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U16) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_242: Core.Ops.Bit.t_Shl t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_243: Core.Ops.Bit.t_Shl t_U32 t_U64 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U64) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_244: Core.Ops.Bit.t_Shl t_U32 t_U128 =
  {
    f_Output = t_U32;
    f_shl_pre = (fun (self: t_U32) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U32) (rhs: t_U128) (out: t_U32) -> true);
    f_shl
    =
    fun (self: t_U32) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_245: Core.Ops.Bit.t_Shr t_U32 t_U8 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U8) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_246: Core.Ops.Bit.t_Shr t_U32 t_U16 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U16) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_247: Core.Ops.Bit.t_Shr t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_248: Core.Ops.Bit.t_Shr t_U32 t_U64 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U64) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_249: Core.Ops.Bit.t_Shr t_U32 t_U128 =
  {
    f_Output = t_U32;
    f_shr_pre = (fun (self: t_U32) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U32) (rhs: t_U128) (out: t_U32) -> true);
    f_shr
    =
    fun (self: t_U32) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_250: Core.Ops.Bit.t_BitXor t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_bitxor_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_bitxor_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_bitxor
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitxor (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_251: Core.Ops.Bit.t_BitAnd t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_bitand_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_bitand_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_bitand
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitand (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_252: Core.Ops.Bit.t_BitOr t_U32 t_U32 =
  {
    f_Output = t_U32;
    f_bitor_pre = (fun (self: t_U32) (rhs: t_U32) -> true);
    f_bitor_post = (fun (self: t_U32) (rhs: t_U32) (out: t_U32) -> true);
    f_bitor
    =
    fun (self: t_U32) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitor (Core.Base_interface.Coerce.f_lift #t_U32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_260: Core.Ops.Arith.t_Neg t_U16 =
  {
    f_Output = t_U16;
    f_neg_pre = (fun (self: t_U16) -> true);
    f_neg_post = (fun (self: t_U16) (out: t_U16) -> true);
    f_neg
    =
    fun (self: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_sub Core.Base.Spec.Constants.v_WORDSIZE_16_
            (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U16
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Haxint.t_HaxInt)
                Core.Base.Spec.Constants.v_WORDSIZE_16_
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_263: Core.Ops.Arith.t_Mul t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_mul_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_mul_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_mul
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_mul (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_264: Core.Ops.Arith.t_Rem t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_rem_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_rem_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_rem
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_265: Core.Ops.Arith.t_Add t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_add_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_add_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_add
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_266: Core.Ops.Arith.t_Div t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_div_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_div_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_div
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_267: Core.Ops.Bit.t_Shl t_U16 t_U8 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U8) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_268: Core.Ops.Bit.t_Shl t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_269: Core.Ops.Bit.t_Shl t_U16 t_U32 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U32) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_270: Core.Ops.Bit.t_Shl t_U16 t_U64 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U64) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_271: Core.Ops.Bit.t_Shl t_U16 t_U128 =
  {
    f_Output = t_U16;
    f_shl_pre = (fun (self: t_U16) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U16) (rhs: t_U128) (out: t_U16) -> true);
    f_shl
    =
    fun (self: t_U16) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_272: Core.Ops.Bit.t_Shr t_U16 t_U8 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U8) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_273: Core.Ops.Bit.t_Shr t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_274: Core.Ops.Bit.t_Shr t_U16 t_U32 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U32) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_275: Core.Ops.Bit.t_Shr t_U16 t_U64 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U64) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_276: Core.Ops.Bit.t_Shr t_U16 t_U128 =
  {
    f_Output = t_U16;
    f_shr_pre = (fun (self: t_U16) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U16) (rhs: t_U128) (out: t_U16) -> true);
    f_shr
    =
    fun (self: t_U16) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_277: Core.Ops.Bit.t_BitXor t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_bitxor_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_bitxor_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_bitxor
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitxor (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_278: Core.Ops.Bit.t_BitAnd t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_bitand_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_bitand_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_bitand
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitand (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_279: Core.Ops.Bit.t_BitOr t_U16 t_U16 =
  {
    f_Output = t_U16;
    f_bitor_pre = (fun (self: t_U16) (rhs: t_U16) -> true);
    f_bitor_post = (fun (self: t_U16) (rhs: t_U16) (out: t_U16) -> true);
    f_bitor
    =
    fun (self: t_U16) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitor (Core.Base_interface.Coerce.f_lift #t_U16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_287: Core.Ops.Arith.t_Neg t_U8 =
  {
    f_Output = t_U8;
    f_neg_pre = (fun (self: t_U8) -> true);
    f_neg_post = (fun (self: t_U8) (out: t_U8) -> true);
    f_neg
    =
    fun (self: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_sub Core.Base.Spec.Constants.v_WORDSIZE_8_
            (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U8
                    #FStar.Tactics.Typeclasses.solve
                    self
                  <:
                  Core.Base.Spec.Haxint.t_HaxInt)
                Core.Base.Spec.Constants.v_WORDSIZE_8_
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_290: Core.Ops.Arith.t_Mul t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_mul_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_mul_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_mul
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_mul (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_291: Core.Ops.Arith.t_Rem t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_rem_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_rem_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_rem
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_rem (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_292: Core.Ops.Arith.t_Add t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_add_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_add_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_add
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_293: Core.Ops.Arith.t_Div t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_div_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_div_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_div
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_294: Core.Ops.Bit.t_Shl t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_295: Core.Ops.Bit.t_Shl t_U8 t_U16 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U16) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U16) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_296: Core.Ops.Bit.t_Shl t_U8 t_U32 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U32) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U32) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_297: Core.Ops.Bit.t_Shl t_U8 t_U64 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U64) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U64) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_298: Core.Ops.Bit.t_Shl t_U8 t_U128 =
  {
    f_Output = t_U8;
    f_shl_pre = (fun (self: t_U8) (rhs: t_U128) -> true);
    f_shl_post = (fun (self: t_U8) (rhs: t_U128) (out: t_U8) -> true);
    f_shl
    =
    fun (self: t_U8) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shl (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_299: Core.Ops.Bit.t_Shr t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_300: Core.Ops.Bit.t_Shr t_U8 t_U16 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U16) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U16) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_301: Core.Ops.Bit.t_Shr t_U8 t_U32 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U32) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U32) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_302: Core.Ops.Bit.t_Shr t_U8 t_U64 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U64) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U64) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_303: Core.Ops.Bit.t_Shr t_U8 t_U128 =
  {
    f_Output = t_U8;
    f_shr_pre = (fun (self: t_U8) (rhs: t_U128) -> true);
    f_shr_post = (fun (self: t_U8) (rhs: t_U128) (out: t_U8) -> true);
    f_shr
    =
    fun (self: t_U8) (rhs: t_U128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_shr (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_304: Core.Ops.Bit.t_BitXor t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_bitxor_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_bitxor_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_bitxor
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitxor (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_305: Core.Ops.Bit.t_BitAnd t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_bitand_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_bitand_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_bitand
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitand (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_306: Core.Ops.Bit.t_BitOr t_U8 t_U8 =
  {
    f_Output = t_U8;
    f_bitor_pre = (fun (self: t_U8) (rhs: t_U8) -> true);
    f_bitor_post = (fun (self: t_U8) (rhs: t_U8) (out: t_U8) -> true);
    f_bitor
    =
    fun (self: t_U8) (rhs: t_U8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
        #t_U8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Pos.haxint_bitor (Core.Base_interface.Coerce.f_lift #t_U8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
            (Core.Base_interface.Coerce.f_lift #t_U8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Ops.Arith.t_Rem t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_rem_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_rem_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_rem
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_rem (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: Core.Ops.Arith.t_Div t_I128 t_I128 =
  {
    f_Output = t_I128;
    f_div_pre = (fun (self: t_I128) (rhs: t_I128) -> true);
    f_div_post = (fun (self: t_I128) (rhs: t_I128) (out: t_I128) -> true);
    f_div
    =
    fun (self: t_I128) (rhs: t_I128) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I128
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #t_I128
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I128 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_73: Core.Ops.Arith.t_Rem t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_rem_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_rem_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_rem
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_rem (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_75: Core.Ops.Arith.t_Div t_I64 t_I64 =
  {
    f_Output = t_I64;
    f_div_pre = (fun (self: t_I64) (rhs: t_I64) -> true);
    f_div_post = (fun (self: t_I64) (rhs: t_I64) (out: t_I64) -> true);
    f_div
    =
    fun (self: t_I64) (rhs: t_I64) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I64
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #t_I64
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I64 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_100: Core.Ops.Arith.t_Rem t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_rem_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_rem_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_rem
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_rem (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_102: Core.Ops.Arith.t_Div t_I32 t_I32 =
  {
    f_Output = t_I32;
    f_div_pre = (fun (self: t_I32) (rhs: t_I32) -> true);
    f_div_post = (fun (self: t_I32) (rhs: t_I32) (out: t_I32) -> true);
    f_div
    =
    fun (self: t_I32) (rhs: t_I32) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I32
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #t_I32
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I32 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_127: Core.Ops.Arith.t_Rem t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_rem_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_rem_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_rem
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_rem (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_129: Core.Ops.Arith.t_Div t_I16 t_I16 =
  {
    f_Output = t_I16;
    f_div_pre = (fun (self: t_I16) (rhs: t_I16) -> true);
    f_div_post = (fun (self: t_I16) (rhs: t_I16) (out: t_I16) -> true);
    f_div
    =
    fun (self: t_I16) (rhs: t_I16) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I16
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #t_I16
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I16 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_154: Core.Ops.Arith.t_Rem t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_rem_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_rem_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_rem
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_rem (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_156: Core.Ops.Arith.t_Div t_I8 t_I8 =
  {
    f_Output = t_I8;
    f_div_pre = (fun (self: t_I8) (rhs: t_I8) -> true);
    f_div_post = (fun (self: t_I8) (rhs: t_I8) (out: t_I8) -> true);
    f_div
    =
    fun (self: t_I8) (rhs: t_I8) ->
      Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
        #t_I8
        #FStar.Tactics.Typeclasses.solve
        (Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #t_I8
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Spec.Z.t_Z)
            (Core.Base_interface.Coerce.f_lift #t_I8 #FStar.Tactics.Typeclasses.solve rhs
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base.Spec.Z.t_Z)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_180: Core.Ops.Arith.t_Sub t_U128 t_U128 =
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
let impl_181: Core.Ops.Bit.t_Not t_U128 =
  {
    f_Output = t_U128;
    f_not_pre = (fun (self: t_U128) -> true);
    f_not_post = (fun (self: t_U128) (out: t_U128) -> true);
    f_not = fun (self: t_U128) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_207: Core.Ops.Arith.t_Sub t_U64 t_U64 =
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
let impl_208: Core.Ops.Bit.t_Not t_U64 =
  {
    f_Output = t_U64;
    f_not_pre = (fun (self: t_U64) -> true);
    f_not_post = (fun (self: t_U64) (out: t_U64) -> true);
    f_not = fun (self: t_U64) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_234: Core.Ops.Arith.t_Sub t_U32 t_U32 =
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
let impl_235: Core.Ops.Bit.t_Not t_U32 =
  {
    f_Output = t_U32;
    f_not_pre = (fun (self: t_U32) -> true);
    f_not_post = (fun (self: t_U32) (out: t_U32) -> true);
    f_not = fun (self: t_U32) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_261: Core.Ops.Arith.t_Sub t_U16 t_U16 =
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
let impl_262: Core.Ops.Bit.t_Not t_U16 =
  {
    f_Output = t_U16;
    f_not_pre = (fun (self: t_U16) -> true);
    f_not_post = (fun (self: t_U16) (out: t_U16) -> true);
    f_not = fun (self: t_U16) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_288: Core.Ops.Arith.t_Sub t_U8 t_U8 =
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
let impl_289: Core.Ops.Bit.t_Not t_U8 =
  {
    f_Output = t_U8;
    f_not_pre = (fun (self: t_U8) -> true);
    f_not_post = (fun (self: t_U8) (out: t_U8) -> true);
    f_not = fun (self: t_U8) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U8)
  }
