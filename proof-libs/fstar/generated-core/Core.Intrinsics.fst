module Core.Intrinsics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Core.Cmp
open Core.Ops.Arith

let unchecked_add_u128 (x y: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Primitive.C_u128
  ({
      Core.Int.f_v
      =
      Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
        (Core.Coerce.f_lift #Core.Int.t_U128 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
    }
    <:
    Core.Int.t_U128)
  <:
  Core.Primitive.t_u128

let unchecked_add_u16 (x y: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Primitive.C_u16
  ({
      Core.Int.f_v
      =
      Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
        (Core.Coerce.f_lift #Core.Int.t_U16 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
    }
    <:
    Core.Int.t_U16)
  <:
  Core.Primitive.t_u16

let unchecked_add_u32 (x y: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Primitive.C_u32
  ({
      Core.Int.f_v
      =
      Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
        (Core.Coerce.f_lift #Core.Int.t_U32 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
    }
    <:
    Core.Int.t_U32)
  <:
  Core.Primitive.t_u32

let unchecked_add_u64 (x y: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Primitive.C_u64
  ({
      Core.Int.f_v
      =
      Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
        (Core.Coerce.f_lift #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
    }
    <:
    Core.Int.t_U64)
  <:
  Core.Primitive.t_u64

let unchecked_add_u8 (x y: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Primitive.C_u8
  ({
      Core.Int.f_v
      =
      Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
        (Core.Coerce.f_lift #Core.Int.t_U8 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
    }
    <:
    Core.Int.t_U8)
  <:
  Core.Primitive.t_u8

let unchecked_add_usize (x y: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Primitive.C_usize
  ({
      Core.Int.f_v
      =
      Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
        (Core.Coerce.f_lift #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
          <:
          Core.Base.Int.t_HaxInt)
    }
    <:
    Core.Int.t_U64)
  <:
  Core.Primitive.t_usize

let add_with_overflow_u128 (x y: Core.Primitive.t_u128) : (Core.Primitive.t_u128 & bool) =
  let overflow:Core.Base.Int.t_HaxInt =
    Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
      (Core.Coerce.f_lift #Core.Int.t_U128 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
  in
  let (res: Core.Int.t_U128):Core.Int.t_U128 =
    Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
      #Core.Int.t_U128
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Int.t_HaxInt)
  in
  (Core.Primitive.C_u128 (Core.Clone.f_clone #Core.Int.t_U128 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u128),
  (Core.Coerce.f_lift #Core.Int.t_U128 #FStar.Tactics.Typeclasses.solve res
    <:
    Core.Base.Int.t_HaxInt) <.
  overflow
  <:
  (Core.Primitive.t_u128 & bool)

let add_with_overflow_u16 (x y: Core.Primitive.t_u16) : (Core.Primitive.t_u16 & bool) =
  let overflow:Core.Base.Int.t_HaxInt =
    Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
      (Core.Coerce.f_lift #Core.Int.t_U16 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
  in
  let (res: Core.Int.t_U16):Core.Int.t_U16 =
    Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
      #Core.Int.t_U16
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Int.t_HaxInt)
  in
  (Core.Primitive.C_u16 (Core.Clone.f_clone #Core.Int.t_U16 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u16),
  (Core.Coerce.f_lift #Core.Int.t_U16 #FStar.Tactics.Typeclasses.solve res <: Core.Base.Int.t_HaxInt
  ) <.
  overflow
  <:
  (Core.Primitive.t_u16 & bool)

let add_with_overflow_u32 (x y: Core.Primitive.t_u32) : (Core.Primitive.t_u32 & bool) =
  let overflow:Core.Base.Int.t_HaxInt =
    Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
      (Core.Coerce.f_lift #Core.Int.t_U32 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
  in
  let (res: Core.Int.t_U32):Core.Int.t_U32 =
    Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
      #Core.Int.t_U32
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Int.t_HaxInt)
  in
  (Core.Primitive.C_u32 (Core.Clone.f_clone #Core.Int.t_U32 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u32),
  (Core.Coerce.f_lift #Core.Int.t_U32 #FStar.Tactics.Typeclasses.solve res <: Core.Base.Int.t_HaxInt
  ) <.
  overflow
  <:
  (Core.Primitive.t_u32 & bool)

let add_with_overflow_u64 (x y: Core.Primitive.t_u64) : (Core.Primitive.t_u64 & bool) =
  let overflow:Core.Base.Int.t_HaxInt =
    Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
      (Core.Coerce.f_lift #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
  in
  let (res: Core.Int.t_U64):Core.Int.t_U64 =
    Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
      #Core.Int.t_U64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Int.t_HaxInt)
  in
  (Core.Primitive.C_u64 (Core.Clone.f_clone #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u64),
  (Core.Coerce.f_lift #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve res <: Core.Base.Int.t_HaxInt
  ) <.
  overflow
  <:
  (Core.Primitive.t_u64 & bool)

let add_with_overflow_u8 (x y: Core.Primitive.t_u8) : (Core.Primitive.t_u8 & bool) =
  let overflow:Core.Base.Int.t_HaxInt =
    Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
      (Core.Coerce.f_lift #Core.Int.t_U8 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
  in
  let (res: Core.Int.t_U8):Core.Int.t_U8 =
    Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
      #Core.Int.t_U8
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Int.t_HaxInt)
  in
  (Core.Primitive.C_u8 (Core.Clone.f_clone #Core.Int.t_U8 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_u8),
  (Core.Coerce.f_lift #Core.Int.t_U8 #FStar.Tactics.Typeclasses.solve res <: Core.Base.Int.t_HaxInt) <.
  overflow
  <:
  (Core.Primitive.t_u8 & bool)

let add_with_overflow_usize (x y: Core.Primitive.t_usize) : (Core.Primitive.t_usize & bool) =
  let overflow:Core.Base.Int.t_HaxInt =
    Core.Base.Int.Base_impl.impl_6__add (Core.Coerce.f_lift #Core.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
      (Core.Coerce.f_lift #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve y.Core.Primitive._0
        <:
        Core.Base.Int.t_HaxInt)
  in
  let (res: Core.Int.t_U64):Core.Int.t_U64 =
    Core.Coerce.f_concretize #Core.Base.Int.t_HaxInt
      #Core.Int.t_U64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Int.t_HaxInt)
  in
  (Core.Primitive.C_usize (Core.Clone.f_clone #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve res)
    <:
    Core.Primitive.t_usize),
  (Core.Coerce.f_lift #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve res <: Core.Base.Int.t_HaxInt
  ) <.
  overflow
  <:
  (Core.Primitive.t_usize & bool)

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
