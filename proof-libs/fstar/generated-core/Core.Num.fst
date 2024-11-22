module Core.Num
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl_10__MAX: Core.Primitive.t_u128 =
  Core.Primitive.C_u128 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_u128

let impl_10__MIN: Core.Primitive.t_u128 =
  Core.Primitive.C_u128 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_u128

let impl_10__from_le (x: Core.Primitive.t_u128) : Core.Primitive.t_u128 = x

let impl_10__to_le (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self

let impl_7__MAX: Core.Primitive.t_u16 =
  Core.Primitive.C_u16 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_u16

let impl_7__MIN: Core.Primitive.t_u16 =
  Core.Primitive.C_u16 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_u16

let impl_7__from_le (x: Core.Primitive.t_u16) : Core.Primitive.t_u16 = x

let impl_7__to_le (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self

let impl__i8__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_97__BITS <: Core.Primitive.t_u32

let impl__i16__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_83__BITS <: Core.Primitive.t_u32

let impl__i32__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_69__BITS <: Core.Primitive.t_u32

let impl__i64__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_55__BITS <: Core.Primitive.t_u32

let impl__i128__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_41__BITS <: Core.Primitive.t_u32

let impl__isize__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_55__BITS <: Core.Primitive.t_u32

let impl_6__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_219__BITS <: Core.Primitive.t_u32

let impl_7__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_192__BITS <: Core.Primitive.t_u32

let impl_8__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_165__BITS <: Core.Primitive.t_u32

let impl_8__MAX: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_u32

let impl_8__MIN: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_u32

let impl_8__from_le (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 = x

let impl_8__to_le (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self

let impl_9__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_138__BITS <: Core.Primitive.t_u32

let impl_10__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_111__BITS <: Core.Primitive.t_u32

let impl_11__BITS: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_138__BITS <: Core.Primitive.t_u32

let impl_9__MAX: Core.Primitive.t_u64 =
  Core.Primitive.C_u64 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_u64

let impl_9__MIN: Core.Primitive.t_u64 =
  Core.Primitive.C_u64 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_u64

let impl_9__from_le (x: Core.Primitive.t_u64) : Core.Primitive.t_u64 = x

let impl_9__to_le (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self

let impl_6__MAX: Core.Primitive.t_u8 =
  Core.Primitive.C_u8 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_u8

let impl_6__MIN: Core.Primitive.t_u8 =
  Core.Primitive.C_u8 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_u8

let impl_6__from_le (x: Core.Primitive.t_u8) : Core.Primitive.t_u8 = x

let impl_6__to_le (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self

let impl_11__MAX: Core.Primitive.t_usize =
  Core.Primitive.C_usize Core.Base_interface.Int.f_MAX <: Core.Primitive.t_usize

let impl_11__MIN: Core.Primitive.t_usize =
  Core.Primitive.C_usize Core.Base_interface.Int.f_MIN <: Core.Primitive.t_usize

let impl_11__from_le (x: Core.Primitive.t_usize) : Core.Primitive.t_usize = x

let impl_11__to_le (self: Core.Primitive.t_usize) : Core.Primitive.t_usize = self

let impl_6__checked_add (self rhs: Core.Primitive.t_u8) : Core.Option.t_Option Core.Primitive.t_u8 =
  Core.Option.Option_Some (Core.Intrinsics.unchecked_add_u8 self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_u8

let impl_7__checked_add (self rhs: Core.Primitive.t_u16) : Core.Option.t_Option Core.Primitive.t_u16 =
  Core.Option.Option_Some (Core.Intrinsics.unchecked_add_u16 self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_u16

let impl_8__checked_add (self rhs: Core.Primitive.t_u32) : Core.Option.t_Option Core.Primitive.t_u32 =
  Core.Option.Option_Some (Core.Intrinsics.unchecked_add_u32 self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_u32

let impl_9__checked_add (self rhs: Core.Primitive.t_u64) : Core.Option.t_Option Core.Primitive.t_u64 =
  Core.Option.Option_Some (Core.Intrinsics.unchecked_add_u64 self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_u64

let impl_10__checked_add (self rhs: Core.Primitive.t_u128)
    : Core.Option.t_Option Core.Primitive.t_u128 =
  Core.Option.Option_Some (Core.Intrinsics.unchecked_add_u128 self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_u128

let impl_11__checked_add (self rhs: Core.Primitive.t_usize)
    : Core.Option.t_Option Core.Primitive.t_usize =
  Core.Option.Option_Some (Core.Intrinsics.unchecked_add_usize self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_usize

let impl__i128__MAX: Core.Primitive.t_i128 =
  Core.Primitive.C_i128 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_i128

let impl__i128__MIN: Core.Primitive.t_i128 =
  Core.Primitive.C_i128 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_i128

let impl__i16__MAX: Core.Primitive.t_i16 =
  Core.Primitive.C_i16 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_i16

let impl__i16__MIN: Core.Primitive.t_i16 =
  Core.Primitive.C_i16 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_i16

let impl__i32__MAX: Core.Primitive.t_i32 =
  Core.Primitive.C_i32 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_i32

let impl__i32__MIN: Core.Primitive.t_i32 =
  Core.Primitive.C_i32 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_i32

let impl__i64__MAX: Core.Primitive.t_i64 =
  Core.Primitive.C_i64 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_i64

let impl__i64__MIN: Core.Primitive.t_i64 =
  Core.Primitive.C_i64 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_i64

let impl__i8__MAX: Core.Primitive.t_i8 =
  Core.Primitive.C_i8 Core.Base_interface.Int.f_MAX <: Core.Primitive.t_i8

let impl__i8__MIN: Core.Primitive.t_i8 =
  Core.Primitive.C_i8 Core.Base_interface.Int.f_MIN <: Core.Primitive.t_i8

let impl__isize__MAX: Core.Primitive.t_isize =
  Core.Primitive.C_isize Core.Base_interface.Int.f_MAX <: Core.Primitive.t_isize

let impl__isize__MIN: Core.Primitive.t_isize =
  Core.Primitive.C_isize Core.Base_interface.Int.f_MIN <: Core.Primitive.t_isize

let impl__i8__is_negative (self: Core.Primitive.t_i8) : bool =
  self <.
  (Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
    <:
    Core.Primitive.t_i8)

let impl__i8__is_positive (self: Core.Primitive.t_i8) : bool =
  self >.
  (Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
    <:
    Core.Primitive.t_i8)

let impl__i8__signum (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  if
    (Core.Clone.f_clone #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve self
      <:
      Core.Primitive.t_i8) <.
    (Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
      <:
      Core.Primitive.t_i8)
  then Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve (-1y)
  else
    if
      self =.
      (Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
        <:
        Core.Primitive.t_i8)
    then Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
    else Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 1y

let impl__i16__is_negative (self: Core.Primitive.t_i16) : bool =
  self <.
  (Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
    <:
    Core.Primitive.t_i16)

let impl__i16__is_positive (self: Core.Primitive.t_i16) : bool =
  self >.
  (Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
    <:
    Core.Primitive.t_i16)

let impl__i16__signum (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  if
    (Core.Clone.f_clone #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve self
      <:
      Core.Primitive.t_i16) <.
    (Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
      <:
      Core.Primitive.t_i16)
  then Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve (-1s)
  else
    if
      self =.
      (Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
        <:
        Core.Primitive.t_i16)
    then Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
    else Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 1s

let impl__i32__is_negative (self: Core.Primitive.t_i32) : bool =
  self <.
  (Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
    <:
    Core.Primitive.t_i32)

let impl__i32__is_positive (self: Core.Primitive.t_i32) : bool =
  self >.
  (Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
    <:
    Core.Primitive.t_i32)

let impl__i32__signum (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  if
    (Core.Clone.f_clone #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve self
      <:
      Core.Primitive.t_i32) <.
    (Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
      <:
      Core.Primitive.t_i32)
  then Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve (-1l)
  else
    if
      self =.
      (Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
        <:
        Core.Primitive.t_i32)
    then Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
    else Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 1l

let impl__i64__is_negative (self: Core.Primitive.t_i64) : bool =
  self <.
  (Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
    <:
    Core.Primitive.t_i64)

let impl__i64__is_positive (self: Core.Primitive.t_i64) : bool =
  self >.
  (Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
    <:
    Core.Primitive.t_i64)

let impl__i64__signum (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  if
    (Core.Clone.f_clone #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve self
      <:
      Core.Primitive.t_i64) <.
    (Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
      <:
      Core.Primitive.t_i64)
  then Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve (-1L)
  else
    if
      self =.
      (Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
        <:
        Core.Primitive.t_i64)
    then Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
    else Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 1L

let impl__i128__is_negative (self: Core.Primitive.t_i128) : bool =
  self <.
  (Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
    <:
    Core.Primitive.t_i128)

let impl__i128__is_positive (self: Core.Primitive.t_i128) : bool =
  self >.
  (Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
    <:
    Core.Primitive.t_i128)

let impl__i128__signum (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  if
    (Core.Clone.f_clone #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve self
      <:
      Core.Primitive.t_i128) <.
    (Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
      <:
      Core.Primitive.t_i128)
  then
    Core.Convert.f_into #i128
      #Core.Primitive.t_i128
      #FStar.Tactics.Typeclasses.solve
      (pub_i128 (-1))
  else
    if
      self =.
      (Core.Convert.f_into #i128
          #Core.Primitive.t_i128
          #FStar.Tactics.Typeclasses.solve
          (pub_i128 0)
        <:
        Core.Primitive.t_i128)
    then
      Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
    else
      Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 1)

let impl__isize__is_negative (self: Core.Primitive.t_isize) : bool =
  self <.
  (Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
    <:
    Core.Primitive.t_isize)

let impl__isize__is_positive (self: Core.Primitive.t_isize) : bool =
  self >.
  (Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
    <:
    Core.Primitive.t_isize)

let impl__isize__signum (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  if
    (Core.Clone.f_clone #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve self
      <:
      Core.Primitive.t_isize) <.
    (Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
      <:
      Core.Primitive.t_isize)
  then
    Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz (-1))
  else
    if
      self =.
      (Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
        <:
        Core.Primitive.t_isize)
    then Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
    else Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 1)

let impl__i8__wrapping_add (self rhs: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  Core.Intrinsics.wrapping_add_i8 self rhs

let impl__i8__wrapping_sub (self rhs: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  Core.Intrinsics.wrapping_sub_i8 self rhs

let impl__i8__wrapping_neg (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  impl__i8__wrapping_sub (Core.Convert.f_into #i8
        #Core.Primitive.t_i8
        #FStar.Tactics.Typeclasses.solve
        0y
      <:
      Core.Primitive.t_i8)
    self

let impl__i8__wrapping_abs (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  if
    impl__i8__is_negative (Core.Clone.f_clone #Core.Primitive.t_i8
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i8)
  then impl__i8__wrapping_neg self
  else self

let impl__i16__wrapping_add (self rhs: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  Core.Intrinsics.wrapping_add_i16 self rhs

let impl__i16__wrapping_sub (self rhs: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  Core.Intrinsics.wrapping_sub_i16 self rhs

let impl__i16__wrapping_neg (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  impl__i16__wrapping_sub (Core.Convert.f_into #i16
        #Core.Primitive.t_i16
        #FStar.Tactics.Typeclasses.solve
        0s
      <:
      Core.Primitive.t_i16)
    self

let impl__i16__wrapping_abs (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  if
    impl__i16__is_negative (Core.Clone.f_clone #Core.Primitive.t_i16
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i16)
  then impl__i16__wrapping_neg self
  else self

let impl__i32__wrapping_add (self rhs: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  Core.Intrinsics.wrapping_add_i32 self rhs

let impl__i32__wrapping_sub (self rhs: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  Core.Intrinsics.wrapping_sub_i32 self rhs

let impl__i32__wrapping_neg (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  impl__i32__wrapping_sub (Core.Convert.f_into #i32
        #Core.Primitive.t_i32
        #FStar.Tactics.Typeclasses.solve
        0l
      <:
      Core.Primitive.t_i32)
    self

let impl__i32__wrapping_abs (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  if
    impl__i32__is_negative (Core.Clone.f_clone #Core.Primitive.t_i32
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i32)
  then impl__i32__wrapping_neg self
  else self

let impl__i64__wrapping_add (self rhs: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  Core.Intrinsics.wrapping_add_i64 self rhs

let impl__i64__wrapping_sub (self rhs: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  Core.Intrinsics.wrapping_sub_i64 self rhs

let impl__i64__wrapping_neg (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  impl__i64__wrapping_sub (Core.Convert.f_into #i64
        #Core.Primitive.t_i64
        #FStar.Tactics.Typeclasses.solve
        0L
      <:
      Core.Primitive.t_i64)
    self

let impl__i64__wrapping_abs (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  if
    impl__i64__is_negative (Core.Clone.f_clone #Core.Primitive.t_i64
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i64)
  then impl__i64__wrapping_neg self
  else self

let impl__i128__wrapping_add (self rhs: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  Core.Intrinsics.wrapping_add_i128 self rhs

let impl__i128__wrapping_sub (self rhs: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  Core.Intrinsics.wrapping_sub_i128 self rhs

let impl__i128__wrapping_neg (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  impl__i128__wrapping_sub (Core.Convert.f_into #i128
        #Core.Primitive.t_i128
        #FStar.Tactics.Typeclasses.solve
        (pub_i128 0)
      <:
      Core.Primitive.t_i128)
    self

let impl__i128__wrapping_abs (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  if
    impl__i128__is_negative (Core.Clone.f_clone #Core.Primitive.t_i128
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i128)
  then impl__i128__wrapping_neg self
  else self

let impl__isize__wrapping_add (self rhs: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  Core.Intrinsics.wrapping_add_isize self rhs

let impl__isize__wrapping_sub (self rhs: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  Core.Intrinsics.wrapping_sub_isize self rhs

let impl__isize__wrapping_neg (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  impl__isize__wrapping_sub (Core.Convert.f_into #isize
        #Core.Primitive.t_isize
        #FStar.Tactics.Typeclasses.solve
        (isz 0)
      <:
      Core.Primitive.t_isize)
    self

let impl__isize__wrapping_abs (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  if
    impl__isize__is_negative (Core.Clone.f_clone #Core.Primitive.t_isize
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_isize)
  then impl__isize__wrapping_neg self
  else self

let impl_6__checked_div (self rhs: Core.Primitive.t_u8) : Core.Option.t_Option Core.Primitive.t_u8 =
  if
    rhs =.
    (Core.Convert.f_into #u8 #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve 0uy
      <:
      Core.Primitive.t_u8)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u8
  else
    Core.Option.Option_Some (Core.Intrinsics.unchecked_div_u8 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u8

let impl_6__overflowing_add (self rhs: Core.Primitive.t_u8) : (Core.Primitive.t_u8 & bool) =
  Core.Intrinsics.add_with_overflow_u8 self rhs

let impl_7__checked_div (self rhs: Core.Primitive.t_u16) : Core.Option.t_Option Core.Primitive.t_u16 =
  if
    rhs =.
    (Core.Convert.f_into #u16 #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve 0us
      <:
      Core.Primitive.t_u16)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u16
  else
    Core.Option.Option_Some (Core.Intrinsics.unchecked_div_u16 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u16

let impl_7__overflowing_add (self rhs: Core.Primitive.t_u16) : (Core.Primitive.t_u16 & bool) =
  Core.Intrinsics.add_with_overflow_u16 self rhs

let impl_8__checked_div (self rhs: Core.Primitive.t_u32) : Core.Option.t_Option Core.Primitive.t_u32 =
  if
    rhs =.
    (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
      <:
      Core.Primitive.t_u32)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u32
  else
    Core.Option.Option_Some (Core.Intrinsics.unchecked_div_u32 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u32

let impl_8__overflowing_add (self rhs: Core.Primitive.t_u32) : (Core.Primitive.t_u32 & bool) =
  Core.Intrinsics.add_with_overflow_u32 self rhs

let impl_9__checked_div (self rhs: Core.Primitive.t_u64) : Core.Option.t_Option Core.Primitive.t_u64 =
  if
    rhs =.
    (Core.Convert.f_into #u64 #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve 0uL
      <:
      Core.Primitive.t_u64)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u64
  else
    Core.Option.Option_Some (Core.Intrinsics.unchecked_div_u64 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u64

let impl_9__overflowing_add (self rhs: Core.Primitive.t_u64) : (Core.Primitive.t_u64 & bool) =
  Core.Intrinsics.add_with_overflow_u64 self rhs

let impl_10__checked_div (self rhs: Core.Primitive.t_u128)
    : Core.Option.t_Option Core.Primitive.t_u128 =
  if
    rhs =.
    (Core.Convert.f_into #u128 #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 0)
      <:
      Core.Primitive.t_u128)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u128
  else
    Core.Option.Option_Some (Core.Intrinsics.unchecked_div_u128 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u128

let impl_10__overflowing_add (self rhs: Core.Primitive.t_u128) : (Core.Primitive.t_u128 & bool) =
  Core.Intrinsics.add_with_overflow_u128 self rhs

let impl_11__checked_div (self rhs: Core.Primitive.t_usize)
    : Core.Option.t_Option Core.Primitive.t_usize =
  if
    rhs =.
    (Core.Convert.f_into #usize #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve (sz 0)
      <:
      Core.Primitive.t_usize)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize
  else
    Core.Option.Option_Some (Core.Intrinsics.unchecked_div_usize self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_usize

let impl_11__overflowing_add (self rhs: Core.Primitive.t_usize) : (Core.Primitive.t_usize & bool) =
  Core.Intrinsics.add_with_overflow_usize self rhs

let impl_6__wrapping_add (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Intrinsics.wrapping_add_u8 self rhs

let impl_6__wrapping_mul (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Intrinsics.wrapping_mul_u8 self rhs

let impl_7__wrapping_add (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Intrinsics.wrapping_add_u16 self rhs

let impl_7__wrapping_mul (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Intrinsics.wrapping_mul_u16 self rhs

let impl_8__wrapping_add (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Intrinsics.wrapping_add_u32 self rhs

let impl_8__wrapping_mul (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Intrinsics.wrapping_mul_u32 self rhs

let impl_9__wrapping_add (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Intrinsics.wrapping_add_u64 self rhs

let impl_9__wrapping_mul (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Intrinsics.wrapping_mul_u64 self rhs

let impl_10__wrapping_add (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Intrinsics.wrapping_add_u128 self rhs

let impl_10__wrapping_mul (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Intrinsics.wrapping_mul_u128 self rhs

let impl_11__wrapping_add (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Intrinsics.wrapping_add_usize self rhs

let impl_11__wrapping_mul (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Intrinsics.wrapping_mul_usize self rhs

let impl__i8__abs (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  if
    impl__i8__is_negative (Core.Clone.f_clone #Core.Primitive.t_i8
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i8)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve self
  else self

let impl__i16__abs (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  if
    impl__i16__is_negative (Core.Clone.f_clone #Core.Primitive.t_i16
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i16)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve self
  else self

let impl__i32__abs (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  if
    impl__i32__is_negative (Core.Clone.f_clone #Core.Primitive.t_i32
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i32)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve self
  else self

let impl__i64__abs (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  if
    impl__i64__is_negative (Core.Clone.f_clone #Core.Primitive.t_i64
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i64)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve self
  else self

let impl__i128__abs (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  if
    impl__i128__is_negative (Core.Clone.f_clone #Core.Primitive.t_i128
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i128)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve self
  else self

let impl__isize__abs (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  if
    impl__isize__is_negative (Core.Clone.f_clone #Core.Primitive.t_isize
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_isize)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve self
  else self

let impl_6__wrapping_sub (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Intrinsics.wrapping_sub_u8 self rhs

let impl_6__wrapping_neg (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  impl_6__wrapping_sub (Core.Primitive.C_u8 Core.Base_interface.Int.f_ZERO <: Core.Primitive.t_u8)
    self

let impl_7__wrapping_sub (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Intrinsics.wrapping_sub_u16 self rhs

let impl_7__wrapping_neg (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  impl_7__wrapping_sub (Core.Primitive.C_u16 Core.Base_interface.Int.f_ZERO <: Core.Primitive.t_u16)
    self

let impl_8__wrapping_sub (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Intrinsics.wrapping_sub_u32 self rhs

let impl_8__wrapping_neg (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  impl_8__wrapping_sub (Core.Primitive.C_u32 Core.Base_interface.Int.f_ZERO <: Core.Primitive.t_u32)
    self

let impl_9__wrapping_sub (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Intrinsics.wrapping_sub_u64 self rhs

let impl_9__wrapping_neg (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  impl_9__wrapping_sub (Core.Primitive.C_u64 Core.Base_interface.Int.f_ZERO <: Core.Primitive.t_u64)
    self

let impl_10__wrapping_sub (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Intrinsics.wrapping_sub_u128 self rhs

let impl_10__wrapping_neg (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  impl_10__wrapping_sub (Core.Primitive.C_u128 Core.Base_interface.Int.f_ZERO
      <:
      Core.Primitive.t_u128)
    self

let impl_11__wrapping_sub (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Intrinsics.wrapping_sub_usize self rhs

let impl_11__wrapping_neg (self: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  impl_11__wrapping_sub (Core.Primitive.C_usize Core.Base_interface.Int.f_ZERO
      <:
      Core.Primitive.t_usize)
    self

let impl_6__wrapping_div (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self /! rhs

let impl_6__wrapping_div_euclid (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self /! rhs

let impl_7__wrapping_div (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self /! rhs

let impl_7__wrapping_div_euclid (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  self /! rhs

let impl_8__wrapping_div (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self /! rhs

let impl_8__wrapping_div_euclid (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  self /! rhs

let impl_9__wrapping_div (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self /! rhs

let impl_9__wrapping_div_euclid (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  self /! rhs

let impl_10__wrapping_div (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self /! rhs

let impl_10__wrapping_div_euclid (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  self /! rhs

let impl_11__wrapping_div (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize = self /! rhs

let impl_11__wrapping_div_euclid (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  self /! rhs

let impl_6__wrapping_rem (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self %! rhs

let impl_6__wrapping_rem_euclid (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self %! rhs

let impl_7__wrapping_rem (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self %! rhs

let impl_7__wrapping_rem_euclid (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  self %! rhs

let impl_8__wrapping_rem (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self %! rhs

let impl_8__wrapping_rem_euclid (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  self %! rhs

let impl_9__wrapping_rem (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self %! rhs

let impl_9__wrapping_rem_euclid (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  self %! rhs

let impl_10__wrapping_rem (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self %! rhs

let impl_10__wrapping_rem_euclid (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  self %! rhs

let impl_11__wrapping_rem (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize = self %! rhs

let impl_11__wrapping_rem_euclid (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  self %! rhs

let impl_6__rotate_left (self: Core.Primitive.t_u8) (n: Core.Primitive.t_u32) : Core.Primitive.t_u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist1:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_left_u8 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u8 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist1)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u8 Core.Primitive.t_u8)

let impl_6__rotate_right (self: Core.Primitive.t_u8) (n: Core.Primitive.t_u32) : Core.Primitive.t_u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist2:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_right_u8 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u8 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist2)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u8 Core.Primitive.t_u8)

let impl_7__rotate_left (self: Core.Primitive.t_u16) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u16 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist3:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_left_u16 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u16 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist3)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u16 Core.Primitive.t_u16)

let impl_7__rotate_right (self: Core.Primitive.t_u16) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u16 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist4:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_right_u16 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u16 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist4)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u16 Core.Primitive.t_u16)

let impl_8__rotate_left (self n: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist5:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_left_u32 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist5)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_8__rotate_right (self n: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist6:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_right_u32 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist6)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_9__rotate_left (self: Core.Primitive.t_u64) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u64 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist7:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_left_u64 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u64 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist7)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u64 Core.Primitive.t_u64)

let impl_9__rotate_right (self: Core.Primitive.t_u64) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u64 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist8:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_right_u64 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u64 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist8)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u64 Core.Primitive.t_u64)

let impl_10__rotate_left (self: Core.Primitive.t_u128) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist9:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_left_u128 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u128 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist9)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u128 Core.Primitive.t_u128)

let impl_10__rotate_right (self: Core.Primitive.t_u128) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist10:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_right_u128 self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u128 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist10)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u128 Core.Primitive.t_u128)

let impl_11__rotate_left (self: Core.Primitive.t_usize) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_usize =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist11:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_left_usize self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_usize Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist11)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_usize Core.Primitive.t_usize)

let impl_11__rotate_right (self: Core.Primitive.t_usize) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_usize =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist12:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.rotate_right_usize self n)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_usize Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist12)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_usize Core.Primitive.t_usize)

let impl_6__count_ones (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist13:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctpop_u8 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist13)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_6__leading_zeros (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist14:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctlz_u8 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist14)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_6__swap_bytes (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Convert.f_into #Core.Primitive.t_u8
    #Core.Primitive.t_u8
    #FStar.Tactics.Typeclasses.solve
    (Core.Intrinsics.bswap_u8 self <: Core.Primitive.t_u8)

let impl_6__from_be (x: Core.Primitive.t_u8) : Core.Primitive.t_u8 = impl_6__swap_bytes x

let impl_6__to_be (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 = impl_6__swap_bytes self

let impl_6__trailing_zeros (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist15:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.cttz_u8 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist15)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_7__count_ones (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist16:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctpop_u16 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist16)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_7__leading_zeros (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist17:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctlz_u16 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist17)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_7__swap_bytes (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Convert.f_into #Core.Primitive.t_u16
    #Core.Primitive.t_u16
    #FStar.Tactics.Typeclasses.solve
    (Core.Intrinsics.bswap_u16 self <: Core.Primitive.t_u16)

let impl_7__from_be (x: Core.Primitive.t_u16) : Core.Primitive.t_u16 = impl_7__swap_bytes x

let impl_7__to_be (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 = impl_7__swap_bytes self

let impl_7__trailing_zeros (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist18:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.cttz_u16 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist18)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_8__count_ones (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist19:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctpop_u32 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist19)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_8__leading_zeros (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist20:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctlz_u32 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist20)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_8__swap_bytes (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Convert.f_into #Core.Primitive.t_u32
    #Core.Primitive.t_u32
    #FStar.Tactics.Typeclasses.solve
    (Core.Intrinsics.bswap_u32 self <: Core.Primitive.t_u32)

let impl_8__from_be (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 = impl_8__swap_bytes x

let impl_8__to_be (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 = impl_8__swap_bytes self

let impl_8__trailing_zeros (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist21:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.cttz_u32 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist21)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_9__count_ones (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist22:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctpop_u64 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist22)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_9__leading_zeros (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist23:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctlz_u64 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist23)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_9__swap_bytes (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Convert.f_into #Core.Primitive.t_u64
    #Core.Primitive.t_u64
    #FStar.Tactics.Typeclasses.solve
    (Core.Intrinsics.bswap_u64 self <: Core.Primitive.t_u64)

let impl_9__from_be (x: Core.Primitive.t_u64) : Core.Primitive.t_u64 = impl_9__swap_bytes x

let impl_9__to_be (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 = impl_9__swap_bytes self

let impl_9__trailing_zeros (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist24:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.cttz_u64 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist24)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_10__count_ones (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist25:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctpop_u128 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist25)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_10__leading_zeros (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist26:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctlz_u128 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist26)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_10__swap_bytes (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Convert.f_into #Core.Primitive.t_u128
    #Core.Primitive.t_u128
    #FStar.Tactics.Typeclasses.solve
    (Core.Intrinsics.bswap_u128 self <: Core.Primitive.t_u128)

let impl_10__from_be (x: Core.Primitive.t_u128) : Core.Primitive.t_u128 = impl_10__swap_bytes x

let impl_10__to_be (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 = impl_10__swap_bytes self

let impl_10__trailing_zeros (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist27:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.cttz_u128 self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist27)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_11__count_ones (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist28:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctpop_usize self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist28)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_11__leading_zeros (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist29:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.ctlz_usize self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist29)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl_11__swap_bytes (self: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Convert.f_into #Core.Primitive.t_usize
    #Core.Primitive.t_usize
    #FStar.Tactics.Typeclasses.solve
    (Core.Intrinsics.bswap_usize self <: Core.Primitive.t_usize)

let impl_11__from_be (x: Core.Primitive.t_usize) : Core.Primitive.t_usize = impl_11__swap_bytes x

let impl_11__to_be (self: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  impl_11__swap_bytes self

let impl_11__trailing_zeros (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! hoist30:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break (Core.Intrinsics.cttz_usize self)
        <:
        Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist30)
      <:
      Core.Ops.Control_flow.t_ControlFlow Core.Primitive.t_u32 Core.Primitive.t_u32)

let impl__i8__rem_euclid (self rhs: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  let r:Core.Primitive.t_i8 =
    self %!
    (Core.Clone.f_clone #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve rhs
      <:
      Core.Primitive.t_i8)
  in
  if
    r <.
    (Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
      <:
      Core.Primitive.t_i8)
  then impl__i8__wrapping_add r (impl__i8__wrapping_abs rhs <: Core.Primitive.t_i8)
  else r

let impl__i16__rem_euclid (self rhs: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  let r:Core.Primitive.t_i16 =
    self %!
    (Core.Clone.f_clone #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve rhs
      <:
      Core.Primitive.t_i16)
  in
  if
    r <.
    (Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
      <:
      Core.Primitive.t_i16)
  then impl__i16__wrapping_add r (impl__i16__wrapping_abs rhs <: Core.Primitive.t_i16)
  else r

let impl__i32__rem_euclid (self rhs: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  let r:Core.Primitive.t_i32 =
    self %!
    (Core.Clone.f_clone #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve rhs
      <:
      Core.Primitive.t_i32)
  in
  if
    r <.
    (Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
      <:
      Core.Primitive.t_i32)
  then impl__i32__wrapping_add r (impl__i32__wrapping_abs rhs <: Core.Primitive.t_i32)
  else r

let impl__i64__rem_euclid (self rhs: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  let r:Core.Primitive.t_i64 =
    self %!
    (Core.Clone.f_clone #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve rhs
      <:
      Core.Primitive.t_i64)
  in
  if
    r <.
    (Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
      <:
      Core.Primitive.t_i64)
  then impl__i64__wrapping_add r (impl__i64__wrapping_abs rhs <: Core.Primitive.t_i64)
  else r

let impl__i128__rem_euclid (self rhs: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  let r:Core.Primitive.t_i128 =
    self %!
    (Core.Clone.f_clone #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve rhs
      <:
      Core.Primitive.t_i128)
  in
  if
    r <.
    (Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
      <:
      Core.Primitive.t_i128)
  then impl__i128__wrapping_add r (impl__i128__wrapping_abs rhs <: Core.Primitive.t_i128)
  else r

let impl__isize__rem_euclid (self rhs: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  let r:Core.Primitive.t_isize =
    self %!
    (Core.Clone.f_clone #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve rhs
      <:
      Core.Primitive.t_isize)
  in
  if
    r <.
    (Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
      <:
      Core.Primitive.t_isize)
  then impl__isize__wrapping_add r (impl__isize__wrapping_abs rhs <: Core.Primitive.t_isize)
  else r

let impl_6__count_zeros (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  impl_6__count_ones (~.self <: Core.Primitive.t_u8)

let impl_6__leading_ones (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  impl_6__leading_zeros (~.self <: Core.Primitive.t_u8)

let impl_6__trailing_ones (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  impl_6__trailing_zeros (~.self <: Core.Primitive.t_u8)

let impl_7__count_zeros (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  impl_7__count_ones (~.self <: Core.Primitive.t_u16)

let impl_7__leading_ones (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  impl_7__leading_zeros (~.self <: Core.Primitive.t_u16)

let impl_7__trailing_ones (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  impl_7__trailing_zeros (~.self <: Core.Primitive.t_u16)

let impl_8__count_zeros (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  impl_8__count_ones (~.self <: Core.Primitive.t_u32)

let impl_8__leading_ones (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  impl_8__leading_zeros (~.self <: Core.Primitive.t_u32)

let impl_8__trailing_ones (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  impl_8__trailing_zeros (~.self <: Core.Primitive.t_u32)

let impl_9__count_zeros (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  impl_9__count_ones (~.self <: Core.Primitive.t_u64)

let impl_9__leading_ones (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  impl_9__leading_zeros (~.self <: Core.Primitive.t_u64)

let impl_9__trailing_ones (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  impl_9__trailing_zeros (~.self <: Core.Primitive.t_u64)

let impl_10__count_zeros (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  impl_10__count_ones (~.self <: Core.Primitive.t_u128)

let impl_10__leading_ones (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  impl_10__leading_zeros (~.self <: Core.Primitive.t_u128)

let impl_10__trailing_ones (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  impl_10__trailing_zeros (~.self <: Core.Primitive.t_u128)

let impl_11__count_zeros (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  impl_11__count_ones (~.self <: Core.Primitive.t_usize)

let impl_11__leading_ones (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  impl_11__leading_zeros (~.self <: Core.Primitive.t_usize)

let impl_11__trailing_ones (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  impl_11__trailing_zeros (~.self <: Core.Primitive.t_usize)
