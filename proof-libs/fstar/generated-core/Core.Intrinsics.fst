module Core.Intrinsics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let unchecked_add_u128 (x y: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Primitive.C_u128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U128)
  <:
  Core.Primitive.t_u128

let unchecked_add_u16 (x y: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Primitive.C_u16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U16)
  <:
  Core.Primitive.t_u16

let unchecked_add_u32 (x y: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Primitive.C_u32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U32)
  <:
  Core.Primitive.t_u32

let unchecked_add_u64 (x y: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Primitive.C_u64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  Core.Primitive.t_u64

let unchecked_add_u8 (x y: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Primitive.C_u8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U8)
  <:
  Core.Primitive.t_u8

let unchecked_add_usize (x y: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Primitive.C_usize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  Core.Primitive.t_usize

let add_with_overflow_i128 (x y: Core.Primitive.t_i128) : (Core.Primitive.t_i128 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I128):Core.Base_interface.Int.t_I128 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I128
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (Core.Primitive.C_i128
    (Core.Clone.f_clone #Core.Base_interface.Int.t_I128 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_i128),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (Core.Primitive.t_i128 & bool)

let unchecked_add_i128 (x y: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  Core.Primitive.C_i128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I128)
  <:
  Core.Primitive.t_i128

let add_with_overflow_i16 (x y: Core.Primitive.t_i16) : (Core.Primitive.t_i16 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I16):Core.Base_interface.Int.t_I16 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I16
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (Core.Primitive.C_i16
    (Core.Clone.f_clone #Core.Base_interface.Int.t_I16 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_i16),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (Core.Primitive.t_i16 & bool)

let unchecked_add_i16 (x y: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  Core.Primitive.C_i16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I16)
  <:
  Core.Primitive.t_i16

let add_with_overflow_i32 (x y: Core.Primitive.t_i32) : (Core.Primitive.t_i32 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I32):Core.Base_interface.Int.t_I32 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I32
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (Core.Primitive.C_i32
    (Core.Clone.f_clone #Core.Base_interface.Int.t_I32 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_i32),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (Core.Primitive.t_i32 & bool)

let unchecked_add_i32 (x y: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  Core.Primitive.C_i32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I32)
  <:
  Core.Primitive.t_i32

let add_with_overflow_i64 (x y: Core.Primitive.t_i64) : (Core.Primitive.t_i64 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I64):Core.Base_interface.Int.t_I64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (Core.Primitive.C_i64
    (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_i64),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (Core.Primitive.t_i64 & bool)

let unchecked_add_i64 (x y: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  Core.Primitive.C_i64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  Core.Primitive.t_i64

let add_with_overflow_i8 (x y: Core.Primitive.t_i8) : (Core.Primitive.t_i8 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I8):Core.Base_interface.Int.t_I8 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I8
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (Core.Primitive.C_i8
    (Core.Clone.f_clone #Core.Base_interface.Int.t_I8 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_i8),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (Core.Primitive.t_i8 & bool)

let unchecked_add_i8 (x y: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  Core.Primitive.C_i8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I8)
  <:
  Core.Primitive.t_i8

let add_with_overflow_isize (x y: Core.Primitive.t_isize) : (Core.Primitive.t_isize & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I64):Core.Base_interface.Int.t_I64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (Core.Primitive.C_isize
    (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_isize),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (Core.Primitive.t_isize & bool)

let unchecked_add_isize (x y: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  Core.Primitive.C_isize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  Core.Primitive.t_isize

let add_with_overflow_u128 (x y: Core.Primitive.t_u128) : (Core.Primitive.t_u128 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U128):Core.Base_interface.Int.t_U128 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U128
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (Core.Primitive.C_u128
    (Core.Clone.f_clone #Core.Base_interface.Int.t_U128 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u128),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (Core.Primitive.t_u128 & bool)

let add_with_overflow_u16 (x y: Core.Primitive.t_u16) : (Core.Primitive.t_u16 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U16):Core.Base_interface.Int.t_U16 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U16
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (Core.Primitive.C_u16
    (Core.Clone.f_clone #Core.Base_interface.Int.t_U16 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u16),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (Core.Primitive.t_u16 & bool)

let add_with_overflow_u32 (x y: Core.Primitive.t_u32) : (Core.Primitive.t_u32 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U32):Core.Base_interface.Int.t_U32 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U32
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (Core.Primitive.C_u32
    (Core.Clone.f_clone #Core.Base_interface.Int.t_U32 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u32),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (Core.Primitive.t_u32 & bool)

let add_with_overflow_u64 (x y: Core.Primitive.t_u64) : (Core.Primitive.t_u64 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U64):Core.Base_interface.Int.t_U64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (Core.Primitive.C_u64
    (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u64),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (Core.Primitive.t_u64 & bool)

let add_with_overflow_u8 (x y: Core.Primitive.t_u8) : (Core.Primitive.t_u8 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U8):Core.Base_interface.Int.t_U8 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U8
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (Core.Primitive.C_u8
    (Core.Clone.f_clone #Core.Base_interface.Int.t_U8 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u8),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (Core.Primitive.t_u8 & bool)

let add_with_overflow_usize (x y: Core.Primitive.t_usize) : (Core.Primitive.t_usize & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          y.Core.Primitive._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U64):Core.Base_interface.Int.t_U64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (Core.Primitive.C_usize
    (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_usize),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (Core.Primitive.t_usize & bool)

let unchecked_div_u128 (x y: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Primitive.C_u128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U128)
  <:
  Core.Primitive.t_u128

let unchecked_div_u16 (x y: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Primitive.C_u16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U16)
  <:
  Core.Primitive.t_u16

let unchecked_div_u32 (x y: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Primitive.C_u32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U32)
  <:
  Core.Primitive.t_u32

let unchecked_div_u64 (x y: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Primitive.C_u64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  Core.Primitive.t_u64

let unchecked_div_u8 (x y: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Primitive.C_u8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U8)
  <:
  Core.Primitive.t_u8

let unchecked_div_usize (x y: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Primitive.C_usize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  Core.Primitive.t_usize

let wrapping_add_i128 (a b: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  Core.Primitive.C_i128 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_i128

let wrapping_add_i16 (a b: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  Core.Primitive.C_i16 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_i16

let wrapping_add_i32 (a b: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  Core.Primitive.C_i32 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_i32

let wrapping_add_i64 (a b: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  Core.Primitive.C_i64 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_i64

let wrapping_add_i8 (a b: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  Core.Primitive.C_i8 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_i8

let wrapping_add_isize (a b: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  Core.Primitive.C_isize (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_isize

let wrapping_sub_i128 (a b: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  Core.Primitive.C_i128 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_i128

let wrapping_sub_i16 (a b: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  Core.Primitive.C_i16 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_i16

let wrapping_sub_i32 (a b: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  Core.Primitive.C_i32 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_i32

let wrapping_sub_i64 (a b: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  Core.Primitive.C_i64 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_i64

let wrapping_sub_i8 (a b: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  Core.Primitive.C_i8 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_i8

let wrapping_sub_isize (a b: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  Core.Primitive.C_isize (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_isize

let unchecked_div_i128 (x y: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  Core.Primitive.C_i128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I128)
  <:
  Core.Primitive.t_i128

let unchecked_div_i16 (x y: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  Core.Primitive.C_i16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I16)
  <:
  Core.Primitive.t_i16

let unchecked_div_i32 (x y: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  Core.Primitive.C_i32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I32)
  <:
  Core.Primitive.t_i32

let unchecked_div_i64 (x y: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  Core.Primitive.C_i64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  Core.Primitive.t_i64

let unchecked_div_i8 (x y: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  Core.Primitive.C_i8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I8)
  <:
  Core.Primitive.t_i8

let unchecked_div_isize (x y: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  Core.Primitive.C_isize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y.Core.Primitive._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  Core.Primitive.t_isize

let wrapping_add_u128 (a b: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Primitive.C_u128 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_u128

let wrapping_add_u16 (a b: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Primitive.C_u16 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_u16

let wrapping_add_u32 (a b: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Primitive.C_u32 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_u32

let wrapping_add_u64 (a b: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Primitive.C_u64 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_u64

let wrapping_add_u8 (a b: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Primitive.C_u8 (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_u8

let wrapping_add_usize (a b: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Primitive.C_usize (a.Core.Primitive._0 +! b.Core.Primitive._0) <: Core.Primitive.t_usize

let wrapping_mul_i128 (a b: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  Core.Primitive.C_i128 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_i128

let wrapping_mul_i16 (a b: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  Core.Primitive.C_i16 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_i16

let wrapping_mul_i32 (a b: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  Core.Primitive.C_i32 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_i32

let wrapping_mul_i64 (a b: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  Core.Primitive.C_i64 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_i64

let wrapping_mul_i8 (a b: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  Core.Primitive.C_i8 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_i8

let wrapping_mul_isize (a b: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  Core.Primitive.C_isize (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_isize

let wrapping_mul_u128 (a b: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Primitive.C_u128 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_u128

let wrapping_mul_u16 (a b: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Primitive.C_u16 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_u16

let wrapping_mul_u32 (a b: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Primitive.C_u32 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_u32

let wrapping_mul_u64 (a b: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Primitive.C_u64 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_u64

let wrapping_mul_u8 (a b: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Primitive.C_u8 (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_u8

let wrapping_mul_usize (a b: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Primitive.C_usize (a.Core.Primitive._0 *! b.Core.Primitive._0) <: Core.Primitive.t_usize

let wrapping_sub_u128 (a b: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Primitive.C_u128 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_u128

let wrapping_sub_u16 (a b: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Primitive.C_u16 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_u16

let wrapping_sub_u32 (a b: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Primitive.C_u32 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_u32

let wrapping_sub_u64 (a b: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Primitive.C_u64 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_u64

let wrapping_sub_u8 (a b: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Primitive.C_u8 (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_u8

let wrapping_sub_usize (a b: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Primitive.C_usize (a.Core.Primitive._0 -! b.Core.Primitive._0) <: Core.Primitive.t_usize

let rotate_left_u128 (x: Core.Primitive.t_u128) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_10__BITS in
  let (left: Core.Primitive.t_u128):Core.Primitive.t_u128 =
    (Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u128) <<!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u128):Core.Primitive.t_u128 =
    (Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u128) >>!
    (Core.Num.impl_10__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u16 (x: Core.Primitive.t_u16) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u16 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_7__BITS in
  let (left: Core.Primitive.t_u16):Core.Primitive.t_u16 =
    (Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u16) <<!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u16):Core.Primitive.t_u16 =
    (Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u16) >>!
    (Core.Num.impl_7__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u32 (x shift: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_8__BITS in
  let (left: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u32) <<!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u32) >>!
    (Core.Num.impl_8__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u64 (x: Core.Primitive.t_u64) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u64 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_9__BITS in
  let (left: Core.Primitive.t_u64):Core.Primitive.t_u64 =
    (Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u64) <<!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u64):Core.Primitive.t_u64 =
    (Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u64) >>!
    (Core.Num.impl_9__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u8 (x: Core.Primitive.t_u8) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u8 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_6__BITS in
  let (left: Core.Primitive.t_u8):Core.Primitive.t_u8 =
    (Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u8) <<!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u8):Core.Primitive.t_u8 =
    (Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u8) >>!
    (Core.Num.impl_6__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_usize (x: Core.Primitive.t_usize) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_usize =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_11__BITS in
  let (left: Core.Primitive.t_usize):Core.Primitive.t_usize =
    (Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_usize) <<!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_usize):Core.Primitive.t_usize =
    (Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_usize) >>!
    (Core.Num.impl_11__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u128 (x: Core.Primitive.t_u128) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_10__BITS in
  let (left: Core.Primitive.t_u128):Core.Primitive.t_u128 =
    (Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u128) >>!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u128):Core.Primitive.t_u128 =
    (Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u128) <<!
    (Core.Num.impl_10__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u16 (x: Core.Primitive.t_u16) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u16 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_7__BITS in
  let (left: Core.Primitive.t_u16):Core.Primitive.t_u16 =
    (Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u16) >>!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u16):Core.Primitive.t_u16 =
    (Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u16) <<!
    (Core.Num.impl_7__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u32 (x shift: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_8__BITS in
  let (left: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u32) >>!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u32) <<!
    (Core.Num.impl_8__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u64 (x: Core.Primitive.t_u64) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u64 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_9__BITS in
  let (left: Core.Primitive.t_u64):Core.Primitive.t_u64 =
    (Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u64) >>!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u64):Core.Primitive.t_u64 =
    (Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u64) <<!
    (Core.Num.impl_9__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u8 (x: Core.Primitive.t_u8) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u8 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_6__BITS in
  let (left: Core.Primitive.t_u8):Core.Primitive.t_u8 =
    (Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u8) >>!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_u8):Core.Primitive.t_u8 =
    (Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_u8) <<!
    (Core.Num.impl_6__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_usize (x: Core.Primitive.t_usize) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_usize =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! Core.Num.impl_11__BITS in
  let (left: Core.Primitive.t_usize):Core.Primitive.t_usize =
    (Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_usize) >>!
    (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
      <:
      Core.Primitive.t_u32)
  in
  let (right: Core.Primitive.t_usize):Core.Primitive.t_usize =
    (Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
      <:
      Core.Primitive.t_usize) <<!
    (Core.Num.impl_11__BITS -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let bswap_u128 (x: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  let (count: Core.Primitive.t_u128):Core.Primitive.t_u128 =
    Core.Convert.f_into #u128 #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 0)
  in
  let count:Core.Primitive.t_u128 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_10__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u128 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u128 = count in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u128):Core.Primitive.t_u128 =
            Core.Convert.f_into #Core.Primitive.t_u128
              #Core.Primitive.t_u128
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u128) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u128) &.
                (Core.Convert.f_into #u128
                    #Core.Primitive.t_u128
                    #FStar.Tactics.Typeclasses.solve
                    (pub_u128 1)
                  <:
                  Core.Primitive.t_u128)
                <:
                Core.Primitive.t_u128)
          in
          let count:Core.Primitive.t_u128 =
            (count <<!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
              <:
              Core.Primitive.t_u128) +!
            low_bit
          in
          count)
  in
  count

let bswap_u16 (x: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  let (count: Core.Primitive.t_u16):Core.Primitive.t_u16 =
    Core.Convert.f_into #u16 #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve 0us
  in
  let count:Core.Primitive.t_u16 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_7__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u16 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u16 = count in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u16):Core.Primitive.t_u16 =
            Core.Convert.f_into #Core.Primitive.t_u16
              #Core.Primitive.t_u16
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u16) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u16) &.
                (Core.Convert.f_into #u16 #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve 1us
                  <:
                  Core.Primitive.t_u16)
                <:
                Core.Primitive.t_u16)
          in
          let count:Core.Primitive.t_u16 =
            (count <<!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
              <:
              Core.Primitive.t_u16) +!
            low_bit
          in
          count)
  in
  count

let bswap_u32 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_8__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u32 = count in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u32
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u32) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32) &.
                (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u32)
          in
          let count:Core.Primitive.t_u32 =
            (count <<!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
              <:
              Core.Primitive.t_u32) +!
            low_bit
          in
          count)
  in
  count

let bswap_u64 (x: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  let (count: Core.Primitive.t_u64):Core.Primitive.t_u64 =
    Core.Convert.f_into #u64 #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve 0uL
  in
  let count:Core.Primitive.t_u64 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_9__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u64 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u64 = count in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u64):Core.Primitive.t_u64 =
            Core.Convert.f_into #Core.Primitive.t_u64
              #Core.Primitive.t_u64
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u64) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u64) &.
                (Core.Convert.f_into #u64 #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve 1uL
                  <:
                  Core.Primitive.t_u64)
                <:
                Core.Primitive.t_u64)
          in
          let count:Core.Primitive.t_u64 =
            (count <<!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
              <:
              Core.Primitive.t_u64) +!
            low_bit
          in
          count)
  in
  count

let bswap_u8 (x: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  let (count: Core.Primitive.t_u8):Core.Primitive.t_u8 =
    Core.Convert.f_into #u8 #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve 0uy
  in
  let count:Core.Primitive.t_u8 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_6__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u8 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u8 = count in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u8):Core.Primitive.t_u8 =
            Core.Convert.f_into #Core.Primitive.t_u8
              #Core.Primitive.t_u8
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u8) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u8) &.
                (Core.Convert.f_into #u8 #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve 1uy
                  <:
                  Core.Primitive.t_u8)
                <:
                Core.Primitive.t_u8)
          in
          let count:Core.Primitive.t_u8 =
            (count <<!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
              <:
              Core.Primitive.t_u8) +!
            low_bit
          in
          count)
  in
  count

let bswap_usize (x: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  let (count: Core.Primitive.t_usize):Core.Primitive.t_usize =
    Core.Convert.f_into #usize #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve (sz 0)
  in
  let count:Core.Primitive.t_usize =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_11__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_usize = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_usize = count in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_usize):Core.Primitive.t_usize =
            Core.Convert.f_into #Core.Primitive.t_usize
              #Core.Primitive.t_usize
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_usize) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_usize) &.
                (Core.Convert.f_into #usize
                    #Core.Primitive.t_usize
                    #FStar.Tactics.Typeclasses.solve
                    (sz 1)
                  <:
                  Core.Primitive.t_usize)
                <:
                Core.Primitive.t_usize)
          in
          let count:Core.Primitive.t_usize =
            (count <<!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
              <:
              Core.Primitive.t_usize) +!
            low_bit
          in
          count)
  in
  count

let ctlz_u128 (x: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_10__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u128
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u128) <<!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u128) >>!
                (Core.Convert.f_into #Core.Primitive.t_u32
                    #Core.Primitive.t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (Core.Num.impl_10__BITS -!
                      (Core.Convert.f_into #u32
                          #Core.Primitive.t_u32
                          #FStar.Tactics.Typeclasses.solve
                          1ul
                        <:
                        Core.Primitive.t_u32)
                      <:
                      Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u128)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let ctlz_u16 (x: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_7__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u16
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u16) <<!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u16) >>!
                (Core.Convert.f_into #Core.Primitive.t_u32
                    #Core.Primitive.t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (Core.Num.impl_7__BITS -!
                      (Core.Convert.f_into #u32
                          #Core.Primitive.t_u32
                          #FStar.Tactics.Typeclasses.solve
                          1ul
                        <:
                        Core.Primitive.t_u32)
                      <:
                      Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u16)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let ctlz_u32 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_8__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u32
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u32) <<!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32) >>!
                (Core.Convert.f_into #Core.Primitive.t_u32
                    #Core.Primitive.t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (Core.Num.impl_8__BITS -!
                      (Core.Convert.f_into #u32
                          #Core.Primitive.t_u32
                          #FStar.Tactics.Typeclasses.solve
                          1ul
                        <:
                        Core.Primitive.t_u32)
                      <:
                      Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u32)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let ctlz_u64 (x: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_9__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u64
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u64) <<!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u64) >>!
                (Core.Convert.f_into #Core.Primitive.t_u32
                    #Core.Primitive.t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (Core.Num.impl_9__BITS -!
                      (Core.Convert.f_into #u32
                          #Core.Primitive.t_u32
                          #FStar.Tactics.Typeclasses.solve
                          1ul
                        <:
                        Core.Primitive.t_u32)
                      <:
                      Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u64)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let ctlz_u8 (x: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_6__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u8
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u8) <<!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u8) >>!
                (Core.Convert.f_into #Core.Primitive.t_u32
                    #Core.Primitive.t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (Core.Num.impl_6__BITS -!
                      (Core.Convert.f_into #u32
                          #Core.Primitive.t_u32
                          #FStar.Tactics.Typeclasses.solve
                          1ul
                        <:
                        Core.Primitive.t_u32)
                      <:
                      Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u8)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let ctlz_usize (x: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_11__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_usize
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_usize) <<!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_usize) >>!
                (Core.Convert.f_into #Core.Primitive.t_u32
                    #Core.Primitive.t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (Core.Num.impl_11__BITS -!
                      (Core.Convert.f_into #u32
                          #Core.Primitive.t_u32
                          #FStar.Tactics.Typeclasses.solve
                          1ul
                        <:
                        Core.Primitive.t_u32)
                      <:
                      Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_usize)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let ctpop_u128 (x: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_10__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #Core.Primitive.t_u128
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u128) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u128) &.
                (Core.Convert.f_into #u128
                    #Core.Primitive.t_u128
                    #FStar.Tactics.Typeclasses.solve
                    (pub_u128 1)
                  <:
                  Core.Primitive.t_u128)
                <:
                Core.Primitive.t_u128)
            <:
            Core.Primitive.t_u32)
          <:
          Core.Primitive.t_u32)
  in
  count

let ctpop_u16 (x: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_7__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #Core.Primitive.t_u16
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u16) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u16) &.
                (Core.Convert.f_into #u16 #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve 1us
                  <:
                  Core.Primitive.t_u16)
                <:
                Core.Primitive.t_u16)
            <:
            Core.Primitive.t_u32)
          <:
          Core.Primitive.t_u32)
  in
  count

let ctpop_u32 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_8__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #Core.Primitive.t_u32
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u32) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32) &.
                (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u32)
            <:
            Core.Primitive.t_u32)
          <:
          Core.Primitive.t_u32)
  in
  count

let ctpop_u64 (x: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_9__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #Core.Primitive.t_u64
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u64) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u64) &.
                (Core.Convert.f_into #u64 #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve 1uL
                  <:
                  Core.Primitive.t_u64)
                <:
                Core.Primitive.t_u64)
            <:
            Core.Primitive.t_u32)
          <:
          Core.Primitive.t_u32)
  in
  count

let ctpop_u8 (x: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_6__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #Core.Primitive.t_u8
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u8) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u8) &.
                (Core.Convert.f_into #u8 #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve 1uy
                  <:
                  Core.Primitive.t_u8)
                <:
                Core.Primitive.t_u8)
            <:
            Core.Primitive.t_u32)
          <:
          Core.Primitive.t_u32)
  in
  count

let ctpop_usize (x: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_11__BITS
        <:
        u32)
      (fun count temp_1_ ->
          let count:Core.Primitive.t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:Core.Primitive.t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #Core.Primitive.t_usize
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_usize) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_usize) &.
                (Core.Convert.f_into #usize
                    #Core.Primitive.t_usize
                    #FStar.Tactics.Typeclasses.solve
                    (sz 1)
                  <:
                  Core.Primitive.t_usize)
                <:
                Core.Primitive.t_usize)
            <:
            Core.Primitive.t_u32)
          <:
          Core.Primitive.t_u32)
  in
  count

let cttz_u128 (x: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_10__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u128
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u128) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u128) &.
                (Core.Convert.f_into #u128
                    #Core.Primitive.t_u128
                    #FStar.Tactics.Typeclasses.solve
                    (pub_u128 1)
                  <:
                  Core.Primitive.t_u128)
                <:
                Core.Primitive.t_u128)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let cttz_u16 (x: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_7__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u16
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u16) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u16) &.
                (Core.Convert.f_into #u16 #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve 1us
                  <:
                  Core.Primitive.t_u16)
                <:
                Core.Primitive.t_u16)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let cttz_u32 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_8__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u32
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u32) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u32) &.
                (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u32)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let cttz_u64 (x: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_9__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u64
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u64) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u64) &.
                (Core.Convert.f_into #u64 #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve 1uL
                  <:
                  Core.Primitive.t_u64)
                <:
                Core.Primitive.t_u64)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let cttz_u8 (x: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_6__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_u8
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_u8) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_u8) &.
                (Core.Convert.f_into #u8 #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve 1uy
                  <:
                  Core.Primitive.t_u8)
                <:
                Core.Primitive.t_u8)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count

let cttz_usize (x: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let done:bool = false in
  let count, done:(Core.Primitive.t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          Core.Num.impl_11__BITS
        <:
        u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (Core.Primitive.t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(Core.Primitive.t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: Core.Primitive.t_u32):Core.Primitive.t_u32 =
            Core.Convert.f_into #Core.Primitive.t_usize
              #Core.Primitive.t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve x
                    <:
                    Core.Primitive.t_usize) >>!
                  (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve i
                    <:
                    Core.Primitive.t_u32)
                  <:
                  Core.Primitive.t_usize) &.
                (Core.Convert.f_into #usize
                    #Core.Primitive.t_usize
                    #FStar.Tactics.Typeclasses.solve
                    (sz 1)
                  <:
                  Core.Primitive.t_usize)
                <:
                Core.Primitive.t_usize)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
              <:
              Core.Primitive.t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (Core.Primitive.t_u32 & bool)
          else
            let count:Core.Primitive.t_u32 =
              count +!
              (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 1ul
                <:
                Core.Primitive.t_u32)
            in
            count, done <: (Core.Primitive.t_u32 & bool))
  in
  count
