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
let impl_51: Core.Clone.t_Clone t_I128 =
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
let impl_57: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I64 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I64) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: Core.Clone.t_Clone t_I64 =
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
let impl_71: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I32 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I32) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_79: Core.Clone.t_Clone t_I32 =
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
let impl_85: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I16 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I16) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_93: Core.Clone.t_Clone t_I16 =
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
let impl_99: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Z.t_Z t_I8 =
  {
    f_concretize_pre = (fun (self: Core.Base.Spec.Z.t_Z) -> true);
    f_concretize_post = (fun (self: Core.Base.Spec.Z.t_Z) (out: t_I8) -> true);
    f_concretize = fun (self: Core.Base.Spec.Z.t_Z) -> { f_v = self } <: t_I8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_107: Core.Clone.t_Clone t_I8 =
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
    f_MIN
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_NEG
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_64_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I128;
    f_MAX
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_POS
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_64_SUB_1_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I128
  }

let impl_41__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_128_ } <: t_U32

let impl_41__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_128_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: t_Constants t_I64 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I64;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I64;
    f_MIN
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_NEG
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_32_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I64;
    f_MAX
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_POS
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_32_SUB_1_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I64
  }

let impl_55__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_64_ } <: t_U32

let impl_55__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_64_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_68: t_Constants t_I32 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I32;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I32;
    f_MIN
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_NEG
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_16_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I32;
    f_MAX
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_POS
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_16_SUB_1_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I32
  }

let impl_69__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_32_ } <: t_U32

let impl_69__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_32_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_82: t_Constants t_I16 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I16;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I16;
    f_MIN
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_NEG
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_8_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I16;
    f_MAX
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_POS
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_8_SUB_1_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I16
  }

let impl_83__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_16_ } <: t_U32

let impl_83__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_16_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_96: t_Constants t_I8 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z } <: t_I8;
    f_ONE
    =
    { f_v = Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z }
    <:
    t_I8;
    f_MIN
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_NEG
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_4_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I8;
    f_MAX
    =
    {
      f_v
      =
      Core.Base.Spec.Z.Z_POS
      (Core.Base.Spec.Binary.Positive.Positive Core.Base.Spec.Constants.v_WORDSIZE_4_SUB_1_
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      <:
      Core.Base.Spec.Z.t_Z
    }
    <:
    t_I8
  }

let impl_97__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_8_ } <: t_U32

let impl_97__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_8_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_110: t_Constants t_U128 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U128;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U128;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U128;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_128_SUB_1_ } <: t_U128
  }

let impl_111__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_128_ } <: t_U32

let impl_111__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_128_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_137: t_Constants t_U64 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U64;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U64;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U64;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_64_SUB_1_ } <: t_U64
  }

let impl_138__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_64_ } <: t_U32

let impl_138__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_64_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_164: t_Constants t_U32 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U32;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U32;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U32;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_32_SUB_1_ } <: t_U32
  }

let impl_165__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_32_ } <: t_U32

let impl_165__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_32_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_191: t_Constants t_U16 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U16;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U16;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U16;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_16_SUB_1_ } <: t_U16
  }

let impl_192__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_16_ } <: t_U32

let impl_192__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_16_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_218: t_Constants t_U8 =
  {
    f_ZERO = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U8;
    f_ONE = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ONE } <: t_U8;
    f_MIN = { f_v = Core.Base.Spec.Haxint.v_HaxInt_ZERO } <: t_U8;
    f_MAX = { f_v = Core.Base.Spec.Constants.v_WORDSIZE_8_SUB_1_ } <: t_U8
  }

let impl_219__BITS: t_U32 = { f_v = Core.Base.Spec.Constants.v_BITS_8_ } <: t_U32

let impl_219__WORDSIZE: Core.Base.Spec.Haxint.t_HaxInt = Core.Base.Spec.Constants.v_WORDSIZE_8_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_134: Core.Clone.t_Clone t_U128 =
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
let impl_161: Core.Clone.t_Clone t_U64 =
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
let impl_188: Core.Clone.t_Clone t_U32 =
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
let impl_215: Core.Clone.t_Clone t_U16 =
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
let impl_242: Core.Clone.t_Clone t_U8 =
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
let impl_52: Core.Cmp.t_PartialEq t_I128 t_I128 =
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
let impl_53: Core.Cmp.t_PartialOrd t_I128 t_I128 =
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
let impl_56: Core.Base_interface.Coerce.t_Abstraction t_I64 =
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
let impl_66: Core.Cmp.t_PartialEq t_I64 t_I64 =
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
let impl_67: Core.Cmp.t_PartialOrd t_I64 t_I64 =
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
let impl_70: Core.Base_interface.Coerce.t_Abstraction t_I32 =
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
let impl_80: Core.Cmp.t_PartialEq t_I32 t_I32 =
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
let impl_81: Core.Cmp.t_PartialOrd t_I32 t_I32 =
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
let impl_84: Core.Base_interface.Coerce.t_Abstraction t_I16 =
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
let impl_94: Core.Cmp.t_PartialEq t_I16 t_I16 =
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
let impl_95: Core.Cmp.t_PartialOrd t_I16 t_I16 =
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
let impl_98: Core.Base_interface.Coerce.t_Abstraction t_I8 =
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
let impl_108: Core.Cmp.t_PartialEq t_I8 t_I8 =
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
let impl_109: Core.Cmp.t_PartialOrd t_I8 t_I8 =
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
let impl_112: Core.Base_interface.Coerce.t_Abstraction t_U128 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U128) -> true);
    f_lift_post = (fun (self: t_U128) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U128) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_135: Core.Cmp.t_PartialEq t_U128 t_U128 =
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
let impl_136: Core.Cmp.t_PartialOrd t_U128 t_U128 =
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
let impl_139: Core.Base_interface.Coerce.t_Abstraction t_U64 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U64) -> true);
    f_lift_post = (fun (self: t_U64) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U64) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_162: Core.Cmp.t_PartialEq t_U64 t_U64 =
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
let impl_163: Core.Cmp.t_PartialOrd t_U64 t_U64 =
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
let impl_166: Core.Base_interface.Coerce.t_Abstraction t_U32 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U32) -> true);
    f_lift_post = (fun (self: t_U32) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U32) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_189: Core.Cmp.t_PartialEq t_U32 t_U32 =
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
let impl_190: Core.Cmp.t_PartialOrd t_U32 t_U32 =
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
let impl_193: Core.Base_interface.Coerce.t_Abstraction t_U16 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U16) -> true);
    f_lift_post = (fun (self: t_U16) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U16) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_216: Core.Cmp.t_PartialEq t_U16 t_U16 =
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
let impl_217: Core.Cmp.t_PartialOrd t_U16 t_U16 =
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
let impl_220: Core.Base_interface.Coerce.t_Abstraction t_U8 =
  {
    f_AbstractType = Core.Base.Spec.Haxint.t_HaxInt;
    f_lift_pre = (fun (self: t_U8) -> true);
    f_lift_post = (fun (self: t_U8) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_lift = fun (self: t_U8) -> self.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_243: Core.Cmp.t_PartialEq t_U8 t_U8 =
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
let impl_244: Core.Cmp.t_PartialOrd t_U8 t_U8 =
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
let impl_48: Core.Ops.Arith.t_Neg t_I128 =
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
let impl_50: Core.Ops.Bit.t_BitOr t_I128 t_I128 =
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
let impl_62: Core.Ops.Arith.t_Neg t_I64 =
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
let impl_64: Core.Ops.Bit.t_BitOr t_I64 t_I64 =
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
let impl_76: Core.Ops.Arith.t_Neg t_I32 =
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
let impl_78: Core.Ops.Bit.t_BitOr t_I32 t_I32 =
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
let impl_90: Core.Ops.Arith.t_Neg t_I16 =
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
let impl_92: Core.Ops.Bit.t_BitOr t_I16 t_I16 =
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
let impl_104: Core.Ops.Arith.t_Neg t_I8 =
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
let impl_106: Core.Ops.Bit.t_BitOr t_I8 t_I8 =
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
let impl_46: Core.Ops.Arith.t_Add t_I128 t_I128 =
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
let impl_49: Core.Ops.Arith.t_Sub t_I128 t_I128 =
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
let impl_60: Core.Ops.Arith.t_Add t_I64 t_I64 =
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
let impl_63: Core.Ops.Arith.t_Sub t_I64 t_I64 =
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
let impl_74: Core.Ops.Arith.t_Add t_I32 t_I32 =
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
let impl_77: Core.Ops.Arith.t_Sub t_I32 t_I32 =
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
let impl_88: Core.Ops.Arith.t_Add t_I16 t_I16 =
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
let impl_91: Core.Ops.Arith.t_Sub t_I16 t_I16 =
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
let impl_102: Core.Ops.Arith.t_Add t_I8 t_I8 =
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
let impl_105: Core.Ops.Arith.t_Sub t_I8 t_I8 =
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
let impl_113: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U128 =
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
let impl_140: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U64 =
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
let impl_167: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U32 =
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
let impl_194: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U16 =
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
let impl_221: Core.Base_interface.Coerce.t_Concretization Core.Base.Spec.Haxint.t_HaxInt t_U8 =
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
let impl_44: Core.Ops.Arith.t_Mul t_I128 t_I128 =
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
let impl_58: Core.Ops.Arith.t_Mul t_I64 t_I64 =
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
let impl_72: Core.Ops.Arith.t_Mul t_I32 t_I32 =
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
let impl_86: Core.Ops.Arith.t_Mul t_I16 t_I16 =
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
let impl_100: Core.Ops.Arith.t_Mul t_I8 t_I8 =
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
let impl_114: Core.Ops.Arith.t_Neg t_U128 =
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
let impl_117: Core.Ops.Arith.t_Mul t_U128 t_U128 =
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
let impl_118: Core.Ops.Arith.t_Rem t_U128 t_U128 =
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
let impl_119: Core.Ops.Arith.t_Add t_U128 t_U128 =
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
let impl_120: Core.Ops.Arith.t_Div t_U128 t_U128 =
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
let impl_121: Core.Ops.Bit.t_Shl t_U128 t_U8 =
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
let impl_122: Core.Ops.Bit.t_Shl t_U128 t_U16 =
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
let impl_123: Core.Ops.Bit.t_Shl t_U128 t_U32 =
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
let impl_124: Core.Ops.Bit.t_Shl t_U128 t_U64 =
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
let impl_125: Core.Ops.Bit.t_Shl t_U128 t_U128 =
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
let impl_126: Core.Ops.Bit.t_Shr t_U128 t_U8 =
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
let impl_127: Core.Ops.Bit.t_Shr t_U128 t_U16 =
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
let impl_128: Core.Ops.Bit.t_Shr t_U128 t_U32 =
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
let impl_129: Core.Ops.Bit.t_Shr t_U128 t_U64 =
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
let impl_130: Core.Ops.Bit.t_Shr t_U128 t_U128 =
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
let impl_131: Core.Ops.Bit.t_BitXor t_U128 t_U128 =
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
let impl_132: Core.Ops.Bit.t_BitAnd t_U128 t_U128 =
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
let impl_133: Core.Ops.Bit.t_BitOr t_U128 t_U128 =
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
let impl_141: Core.Ops.Arith.t_Neg t_U64 =
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
let impl_144: Core.Ops.Arith.t_Mul t_U64 t_U64 =
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
let impl_145: Core.Ops.Arith.t_Rem t_U64 t_U64 =
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
let impl_146: Core.Ops.Arith.t_Add t_U64 t_U64 =
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
let impl_147: Core.Ops.Arith.t_Div t_U64 t_U64 =
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
let impl_148: Core.Ops.Bit.t_Shl t_U64 t_U8 =
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
let impl_149: Core.Ops.Bit.t_Shl t_U64 t_U16 =
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
let impl_150: Core.Ops.Bit.t_Shl t_U64 t_U32 =
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
let impl_151: Core.Ops.Bit.t_Shl t_U64 t_U64 =
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
let impl_152: Core.Ops.Bit.t_Shl t_U64 t_U128 =
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
let impl_153: Core.Ops.Bit.t_Shr t_U64 t_U8 =
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
let impl_154: Core.Ops.Bit.t_Shr t_U64 t_U16 =
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
let impl_155: Core.Ops.Bit.t_Shr t_U64 t_U32 =
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
let impl_156: Core.Ops.Bit.t_Shr t_U64 t_U64 =
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
let impl_157: Core.Ops.Bit.t_Shr t_U64 t_U128 =
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
let impl_158: Core.Ops.Bit.t_BitXor t_U64 t_U64 =
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
let impl_159: Core.Ops.Bit.t_BitAnd t_U64 t_U64 =
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
let impl_160: Core.Ops.Bit.t_BitOr t_U64 t_U64 =
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
let impl_168: Core.Ops.Arith.t_Neg t_U32 =
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
let impl_171: Core.Ops.Arith.t_Mul t_U32 t_U32 =
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
let impl_172: Core.Ops.Arith.t_Rem t_U32 t_U32 =
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
let impl_173: Core.Ops.Arith.t_Add t_U32 t_U32 =
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
let impl_174: Core.Ops.Arith.t_Div t_U32 t_U32 =
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
let impl_175: Core.Ops.Bit.t_Shl t_U32 t_U8 =
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
let impl_176: Core.Ops.Bit.t_Shl t_U32 t_U16 =
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
let impl_177: Core.Ops.Bit.t_Shl t_U32 t_U32 =
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
let impl_178: Core.Ops.Bit.t_Shl t_U32 t_U64 =
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
let impl_179: Core.Ops.Bit.t_Shl t_U32 t_U128 =
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
let impl_180: Core.Ops.Bit.t_Shr t_U32 t_U8 =
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
let impl_181: Core.Ops.Bit.t_Shr t_U32 t_U16 =
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
let impl_182: Core.Ops.Bit.t_Shr t_U32 t_U32 =
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
let impl_183: Core.Ops.Bit.t_Shr t_U32 t_U64 =
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
let impl_184: Core.Ops.Bit.t_Shr t_U32 t_U128 =
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
let impl_185: Core.Ops.Bit.t_BitXor t_U32 t_U32 =
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
let impl_186: Core.Ops.Bit.t_BitAnd t_U32 t_U32 =
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
let impl_187: Core.Ops.Bit.t_BitOr t_U32 t_U32 =
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
let impl_195: Core.Ops.Arith.t_Neg t_U16 =
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
let impl_198: Core.Ops.Arith.t_Mul t_U16 t_U16 =
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
let impl_199: Core.Ops.Arith.t_Rem t_U16 t_U16 =
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
let impl_200: Core.Ops.Arith.t_Add t_U16 t_U16 =
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
let impl_201: Core.Ops.Arith.t_Div t_U16 t_U16 =
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
let impl_202: Core.Ops.Bit.t_Shl t_U16 t_U8 =
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
let impl_203: Core.Ops.Bit.t_Shl t_U16 t_U16 =
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
let impl_204: Core.Ops.Bit.t_Shl t_U16 t_U32 =
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
let impl_205: Core.Ops.Bit.t_Shl t_U16 t_U64 =
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
let impl_206: Core.Ops.Bit.t_Shl t_U16 t_U128 =
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
let impl_207: Core.Ops.Bit.t_Shr t_U16 t_U8 =
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
let impl_208: Core.Ops.Bit.t_Shr t_U16 t_U16 =
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
let impl_209: Core.Ops.Bit.t_Shr t_U16 t_U32 =
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
let impl_210: Core.Ops.Bit.t_Shr t_U16 t_U64 =
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
let impl_211: Core.Ops.Bit.t_Shr t_U16 t_U128 =
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
let impl_212: Core.Ops.Bit.t_BitXor t_U16 t_U16 =
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
let impl_213: Core.Ops.Bit.t_BitAnd t_U16 t_U16 =
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
let impl_214: Core.Ops.Bit.t_BitOr t_U16 t_U16 =
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
let impl_222: Core.Ops.Arith.t_Neg t_U8 =
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
let impl_225: Core.Ops.Arith.t_Mul t_U8 t_U8 =
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
let impl_226: Core.Ops.Arith.t_Rem t_U8 t_U8 =
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
let impl_227: Core.Ops.Arith.t_Add t_U8 t_U8 =
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
let impl_228: Core.Ops.Arith.t_Div t_U8 t_U8 =
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
let impl_229: Core.Ops.Bit.t_Shl t_U8 t_U8 =
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
let impl_230: Core.Ops.Bit.t_Shl t_U8 t_U16 =
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
let impl_231: Core.Ops.Bit.t_Shl t_U8 t_U32 =
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
let impl_232: Core.Ops.Bit.t_Shl t_U8 t_U64 =
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
let impl_233: Core.Ops.Bit.t_Shl t_U8 t_U128 =
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
let impl_234: Core.Ops.Bit.t_Shr t_U8 t_U8 =
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
let impl_235: Core.Ops.Bit.t_Shr t_U8 t_U16 =
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
let impl_236: Core.Ops.Bit.t_Shr t_U8 t_U32 =
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
let impl_237: Core.Ops.Bit.t_Shr t_U8 t_U64 =
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
let impl_238: Core.Ops.Bit.t_Shr t_U8 t_U128 =
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
let impl_239: Core.Ops.Bit.t_BitXor t_U8 t_U8 =
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
let impl_240: Core.Ops.Bit.t_BitAnd t_U8 t_U8 =
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
let impl_241: Core.Ops.Bit.t_BitOr t_U8 t_U8 =
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
let impl_45: Core.Ops.Arith.t_Rem t_I128 t_I128 =
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
let impl_47: Core.Ops.Arith.t_Div t_I128 t_I128 =
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
let impl_59: Core.Ops.Arith.t_Rem t_I64 t_I64 =
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
let impl_61: Core.Ops.Arith.t_Div t_I64 t_I64 =
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
let impl_73: Core.Ops.Arith.t_Rem t_I32 t_I32 =
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
let impl_75: Core.Ops.Arith.t_Div t_I32 t_I32 =
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
let impl_87: Core.Ops.Arith.t_Rem t_I16 t_I16 =
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
let impl_89: Core.Ops.Arith.t_Div t_I16 t_I16 =
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
let impl_101: Core.Ops.Arith.t_Rem t_I8 t_I8 =
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
let impl_103: Core.Ops.Arith.t_Div t_I8 t_I8 =
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
let impl_115: Core.Ops.Arith.t_Sub t_U128 t_U128 =
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
let impl_116: Core.Ops.Bit.t_Not t_U128 =
  {
    f_Output = t_U128;
    f_not_pre = (fun (self: t_U128) -> true);
    f_not_post = (fun (self: t_U128) (out: t_U128) -> true);
    f_not = fun (self: t_U128) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_142: Core.Ops.Arith.t_Sub t_U64 t_U64 =
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
let impl_143: Core.Ops.Bit.t_Not t_U64 =
  {
    f_Output = t_U64;
    f_not_pre = (fun (self: t_U64) -> true);
    f_not_post = (fun (self: t_U64) (out: t_U64) -> true);
    f_not = fun (self: t_U64) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_169: Core.Ops.Arith.t_Sub t_U32 t_U32 =
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
let impl_170: Core.Ops.Bit.t_Not t_U32 =
  {
    f_Output = t_U32;
    f_not_pre = (fun (self: t_U32) -> true);
    f_not_post = (fun (self: t_U32) (out: t_U32) -> true);
    f_not = fun (self: t_U32) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_196: Core.Ops.Arith.t_Sub t_U16 t_U16 =
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
let impl_197: Core.Ops.Bit.t_Not t_U16 =
  {
    f_Output = t_U16;
    f_not_pre = (fun (self: t_U16) -> true);
    f_not_post = (fun (self: t_U16) (out: t_U16) -> true);
    f_not = fun (self: t_U16) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_223: Core.Ops.Arith.t_Sub t_U8 t_U8 =
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
let impl_224: Core.Ops.Bit.t_Not t_U8 =
  {
    f_Output = t_U8;
    f_not_pre = (fun (self: t_U8) -> true);
    f_not_post = (fun (self: t_U8) (out: t_U8) -> true);
    f_not = fun (self: t_U8) -> self ^. (f_MAX #FStar.Tactics.Typeclasses.solve <: t_U8)
  }
