module Core.Intrinsics.Rec_bundle_253787241
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

let from_le715594649 (x: Core.Primitive.t_u128) : Core.Primitive.t_u128 = x

let to_le902648378 (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self

let from_le793045973 (x: Core.Primitive.t_u16) : Core.Primitive.t_u16 = x

let to_le1012469456 (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self

let from_le706338679 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 = x

let to_le724624277 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self

let from_le435089922 (x: Core.Primitive.t_u64) : Core.Primitive.t_u64 = x

let to_le2703875 (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self

let from_le529489651 (x: Core.Primitive.t_u8) : Core.Primitive.t_u8 = x

let to_le523556665 (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self

let from_le418743864 (x: Core.Primitive.t_usize) : Core.Primitive.t_usize = x

let to_le946822077 (self: Core.Primitive.t_usize) : Core.Primitive.t_usize = self

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

let v_BITS80497669: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_149__BITS <: Core.Primitive.t_u32

let v_MAX626626007: Core.Primitive.t_i8 =
  Core.Primitive.C_i8 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i8

let v_MIN19747349: Core.Primitive.t_i8 =
  Core.Primitive.C_i8 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i8

let v_BITS421056295: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_122__BITS <: Core.Primitive.t_u32

let v_MAX474501300: Core.Primitive.t_i16 =
  Core.Primitive.C_i16 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i16

let v_MIN776391606: Core.Primitive.t_i16 =
  Core.Primitive.C_i16 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i16

let v_BITS465526498: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_95__BITS <: Core.Primitive.t_u32

let v_MAX106630818: Core.Primitive.t_i32 =
  Core.Primitive.C_i32 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i32

let v_MIN682967538: Core.Primitive.t_i32 =
  Core.Primitive.C_i32 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i32

let v_BITS419886578: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_68__BITS <: Core.Primitive.t_u32

let v_MAX527043787: Core.Primitive.t_i64 =
  Core.Primitive.C_i64 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i64

let v_MIN654206259: Core.Primitive.t_i64 =
  Core.Primitive.C_i64 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i64

let v_BITS992667165: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_41__BITS <: Core.Primitive.t_u32

let v_MAX375377319: Core.Primitive.t_i128 =
  Core.Primitive.C_i128 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i128

let v_MIN79612531: Core.Primitive.t_i128 =
  Core.Primitive.C_i128 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_i128

let v_BITS211584016: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_68__BITS <: Core.Primitive.t_u32

let v_MAX937003029: Core.Primitive.t_isize =
  Core.Primitive.C_isize (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_isize

let v_MIN1017039533: Core.Primitive.t_isize =
  Core.Primitive.C_isize (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_isize

let v_BITS690311813: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_284__BITS <: Core.Primitive.t_u32

let v_MAX310118176: Core.Primitive.t_u8 =
  Core.Primitive.C_u8 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u8

let v_MIN41851434: Core.Primitive.t_u8 =
  Core.Primitive.C_u8 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u8

let v_BITS277333551: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_257__BITS <: Core.Primitive.t_u32

let v_MAX487295910: Core.Primitive.t_u16 =
  Core.Primitive.C_u16 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u16

let v_MIN592300287: Core.Primitive.t_u16 =
  Core.Primitive.C_u16 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u16

let v_BITS473478051: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_230__BITS <: Core.Primitive.t_u32

let v_MAX826434525: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u32

let v_MIN932777089: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u32

let v_BITS177666292: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_203__BITS <: Core.Primitive.t_u32

let v_MAX815180633: Core.Primitive.t_u64 =
  Core.Primitive.C_u64 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u64

let v_MIN631333594: Core.Primitive.t_u64 =
  Core.Primitive.C_u64 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u64

let v_BITS136999051: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_176__BITS <: Core.Primitive.t_u32

let v_MAX404543799: Core.Primitive.t_u128 =
  Core.Primitive.C_u128 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u128

let v_MIN668621698: Core.Primitive.t_u128 =
  Core.Primitive.C_u128 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_u128

let v_BITS229952196: Core.Primitive.t_u32 =
  Core.Primitive.C_u32 Core.Base_interface.Int.impl_203__BITS <: Core.Primitive.t_u32

let v_MAX750570916: Core.Primitive.t_usize =
  Core.Primitive.C_usize (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_usize

let v_MIN861571008: Core.Primitive.t_usize =
  Core.Primitive.C_usize (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve)
  <:
  Core.Primitive.t_usize

let rec from_u128_binary (x: u128)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U128.ne x (pub_u128 0))
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U128.eq x (pub_u128 1)
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U128.eq (Rust_primitives.U128.rem x (pub_u128 2) <: u128) (pub_u128 0)
    then
      Core.Base.Spec.Binary.Positive.xO (from_u128_binary (Rust_primitives.U128.div x (pub_u128 2)
              <:
              u128)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u128_binary (Rust_primitives.U128.div x (pub_u128 2)
              <:
              u128)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u128 =
  {
    f_from_pre = (fun (x: u128) -> true);
    f_from_post = (fun (x: u128) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u128) ->
      if Rust_primitives.U128.eq x (pub_u128 0)
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u128_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From Core.Base.Spec.Z.t_Z i128 =
  {
    f_from_pre = (fun (x: i128) -> true);
    f_from_post = (fun (x: i128) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i128) ->
      match Core.Cmp.f_cmp #i128 #FStar.Tactics.Typeclasses.solve x (pub_i128 0) with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u128_binary (Core.Num.impl__i128__unsigned_abs x <: u128))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u128_binary (Core.Num.impl__i128__unsigned_abs x <: u128))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u16_binary (x: u16)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U16.ne x 0us)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U16.eq x 1us
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U16.eq (Rust_primitives.U16.rem x 2us <: u16) 0us
    then
      Core.Base.Spec.Binary.Positive.xO (from_u16_binary (Rust_primitives.U16.div x 2us <: u16)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u16_binary (Rust_primitives.U16.div x 2us <: u16)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u16) ->
      if Rust_primitives.U16.eq x 0us
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u16_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From Core.Base.Spec.Z.t_Z i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i16) ->
      match Core.Cmp.f_cmp #i16 #FStar.Tactics.Typeclasses.solve x 0s with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u16_binary (Core.Num.impl_1__unsigned_abs x <: u16))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u16_binary (Core.Num.impl_1__unsigned_abs x <: u16))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u32_binary (x: u32)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U32.ne x 0ul)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U32.eq x 1ul
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U32.eq (Rust_primitives.U32.rem x 2ul <: u32) 0ul
    then
      Core.Base.Spec.Binary.Positive.xO (from_u32_binary (Rust_primitives.U32.div x 2ul <: u32)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u32_binary (Rust_primitives.U32.div x 2ul <: u32)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u32) ->
      if Rust_primitives.U32.eq x 0ul
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u32_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From Core.Base.Spec.Z.t_Z i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i32) ->
      match Core.Cmp.f_cmp #i32 #FStar.Tactics.Typeclasses.solve x 0l with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u32_binary (Core.Num.impl__i32__unsigned_abs x <: u32))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u32_binary (Core.Num.impl__i32__unsigned_abs x <: u32))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u64_binary (x: u64)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U64.ne x 0uL)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U64.eq x 1uL
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U64.eq (Rust_primitives.U64.rem x 2uL <: u64) 0uL
    then
      Core.Base.Spec.Binary.Positive.xO (from_u64_binary (Rust_primitives.U64.div x 2uL <: u64)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u64_binary (Rust_primitives.U64.div x 2uL <: u64)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u64 =
  {
    f_from_pre = (fun (x: u64) -> true);
    f_from_post = (fun (x: u64) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u64) ->
      if Rust_primitives.U64.eq x 0uL
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u64_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From Core.Base.Spec.Z.t_Z i64 =
  {
    f_from_pre = (fun (x: i64) -> true);
    f_from_post = (fun (x: i64) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i64) ->
      match Core.Cmp.f_cmp #i64 #FStar.Tactics.Typeclasses.solve x 0L with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u64_binary (Core.Num.impl__i64__unsigned_abs x <: u64))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u64_binary (Core.Num.impl__i64__unsigned_abs x <: u64))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u8_binary (x: u8)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U8.ne x 0uy)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U8.eq x 1uy
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U8.eq (Rust_primitives.U8.rem x 2uy <: u8) 0uy
    then
      Core.Base.Spec.Binary.Positive.xO (from_u8_binary (Rust_primitives.U8.div x 2uy <: u8)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u8_binary (Rust_primitives.U8.div x 2uy <: u8)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u8) ->
      if Rust_primitives.U8.eq x 0uy
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u8_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From Core.Base.Spec.Z.t_Z i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i8) ->
      match Core.Cmp.f_cmp #i8 #FStar.Tactics.Typeclasses.solve x 0y with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u8_binary (Core.Num.impl__unsigned_abs x <: u8))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u8_binary (Core.Num.impl__unsigned_abs x <: u8))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_usize_binary (x: usize)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.Usize.ne x (sz 0))
      (fun _ -> Prims.l_True) =
  if Rust_primitives.Usize.eq x (sz 1)
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.Usize.eq (Rust_primitives.Usize.rem x (sz 2) <: usize) (sz 0)
    then
      Core.Base.Spec.Binary.Positive.xO (from_usize_binary (Rust_primitives.Usize.div x (sz 2)
              <:
              usize)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_usize_binary (Rust_primitives.Usize.div x (sz 2)
              <:
              usize)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt usize =
  {
    f_from_pre = (fun (x: usize) -> true);
    f_from_post = (fun (x: usize) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: usize) ->
      if Rust_primitives.Usize.eq x (sz 0)
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_usize_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From Core.Base.Spec.Z.t_Z isize =
  {
    f_from_pre = (fun (x: isize) -> true);
    f_from_post = (fun (x: isize) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: isize) ->
      match Core.Cmp.f_cmp #isize #FStar.Tactics.Typeclasses.solve x (isz 0) with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_usize_binary (Core.Num.impl__isize__unsigned_abs x <: usize))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_usize_binary (Core.Num.impl__isize__unsigned_abs x <: usize))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec to_u128_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u128 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> pub_u128 1
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U128.mul (to_u128_binary p <: u128) (pub_u128 2)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U128.add (Rust_primitives.U128.mul (to_u128_binary p <: u128) (pub_u128 2)
        <:
        u128)
      (pub_u128 1)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From u128 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u128) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> pub_u128 0
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u128_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Convert.t_From i128 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i128) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I128.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U128.sub (to_u128_binary
                          x
                        <:
                        u128)
                      (pub_u128 1)
                    <:
                    u128)
                <:
                i128)
            <:
            i128)
          (pub_i128 1)
      | Core.Base.Spec.Z.Z_ZERO  -> pub_i128 0
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u128_binary x <: u128) <: i128
  }

let rec to_u16_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u16 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1us
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U16.mul (to_u16_binary p <: u16) 2us
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U16.add (Rust_primitives.U16.mul (to_u16_binary p <: u16) 2us <: u16) 1us

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From u16 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u16) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0us
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u16_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From i16 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i16) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I16.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U16.sub (to_u16_binary
                          x
                        <:
                        u16)
                      1us
                    <:
                    u16)
                <:
                i16)
            <:
            i16)
          1s
      | Core.Base.Spec.Z.Z_ZERO  -> 0s
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u16_binary x <: u16) <: i16
  }

let rec to_u32_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u32 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1ul
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U32.mul (to_u32_binary p <: u32) 2ul
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U32.add (Rust_primitives.U32.mul (to_u32_binary p <: u32) 2ul <: u32) 1ul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From u32 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u32) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0ul
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u32_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From i32 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i32) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I32.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U32.sub (to_u32_binary
                          x
                        <:
                        u32)
                      1ul
                    <:
                    u32)
                <:
                i32)
            <:
            i32)
          1l
      | Core.Base.Spec.Z.Z_ZERO  -> 0l
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u32_binary x <: u32) <: i32
  }

let rec to_u64_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u64 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1uL
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U64.mul (to_u64_binary p <: u64) 2uL
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U64.add (Rust_primitives.U64.mul (to_u64_binary p <: u64) 2uL <: u64) 1uL

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From u64 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u64) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0uL
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u64_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From i64 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i64) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I64.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U64.sub (to_u64_binary
                          x
                        <:
                        u64)
                      1uL
                    <:
                    u64)
                <:
                i64)
            <:
            i64)
          1L
      | Core.Base.Spec.Z.Z_ZERO  -> 0L
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u64_binary x <: u64) <: i64
  }

let rec to_u8_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u8 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1uy
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U8.mul (to_u8_binary p <: u8) 2uy
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U8.add (Rust_primitives.U8.mul (to_u8_binary p <: u8) 2uy <: u8) 1uy

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From u8 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u8) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0uy
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u8_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From i8 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i8) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I8.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U8.sub (to_u8_binary x
                        <:
                        u8)
                      1uy
                    <:
                    u8)
                <:
                i8)
            <:
            i8)
          1y
      | Core.Base.Spec.Z.Z_ZERO  -> 0y
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u8_binary x <: u8) <: i8
  }

let rec to_usize_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : usize =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> sz 1
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.Usize.mul (to_usize_binary p <: usize) (sz 2)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.Usize.add (Rust_primitives.Usize.mul (to_usize_binary p <: usize) (sz 2)
        <:
        usize)
      (sz 1)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From usize Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: usize) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> sz 0
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_usize_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From isize Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: isize) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.Isize.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.Usize.sub (to_usize_binary
                          x
                        <:
                        usize)
                      (sz 1)
                    <:
                    usize)
                <:
                isize)
            <:
            isize)
          (isz 1)
      | Core.Base.Spec.Z.Z_ZERO  -> isz 0
      | Core.Base.Spec.Z.Z_POS x -> cast (to_usize_binary x <: usize) <: isize
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

let is_negative350273175 (self: Core.Primitive.t_i8) : bool =
  self <.
  (Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
    <:
    Core.Primitive.t_i8)

let is_positive286955196 (self: Core.Primitive.t_i8) : bool =
  self >.
  (Core.Convert.f_into #i8 #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve 0y
    <:
    Core.Primitive.t_i8)

let signum721334203 (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
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

let is_negative477067241 (self: Core.Primitive.t_i16) : bool =
  self <.
  (Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
    <:
    Core.Primitive.t_i16)

let is_positive821581438 (self: Core.Primitive.t_i16) : bool =
  self >.
  (Core.Convert.f_into #i16 #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve 0s
    <:
    Core.Primitive.t_i16)

let signum243706004 (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
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

let is_negative1035644813 (self: Core.Primitive.t_i32) : bool =
  self <.
  (Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
    <:
    Core.Primitive.t_i32)

let is_positive401652342 (self: Core.Primitive.t_i32) : bool =
  self >.
  (Core.Convert.f_into #i32 #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve 0l
    <:
    Core.Primitive.t_i32)

let signum323641039 (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
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

let is_negative1066124578 (self: Core.Primitive.t_i64) : bool =
  self <.
  (Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
    <:
    Core.Primitive.t_i64)

let is_positive16569358 (self: Core.Primitive.t_i64) : bool =
  self >.
  (Core.Convert.f_into #i64 #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve 0L
    <:
    Core.Primitive.t_i64)

let signum582963664 (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
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

let is_negative221698470 (self: Core.Primitive.t_i128) : bool =
  self <.
  (Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
    <:
    Core.Primitive.t_i128)

let is_positive883218309 (self: Core.Primitive.t_i128) : bool =
  self >.
  (Core.Convert.f_into #i128 #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
    <:
    Core.Primitive.t_i128)

let signum408800799 (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
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

let is_negative693446369 (self: Core.Primitive.t_isize) : bool =
  self <.
  (Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
    <:
    Core.Primitive.t_isize)

let is_positive169998680 (self: Core.Primitive.t_isize) : bool =
  self >.
  (Core.Convert.f_into #isize #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
    <:
    Core.Primitive.t_isize)

let signum91486536 (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
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

let checked_add268751055 (self rhs: Core.Primitive.t_u8) : Core.Option.t_Option Core.Primitive.t_u8 =
  Core.Option.Option_Some (unchecked_add_u8 self rhs) <: Core.Option.t_Option Core.Primitive.t_u8

let checked_add132377399 (self rhs: Core.Primitive.t_u16)
    : Core.Option.t_Option Core.Primitive.t_u16 =
  Core.Option.Option_Some (unchecked_add_u16 self rhs) <: Core.Option.t_Option Core.Primitive.t_u16

let checked_add985437730 (self rhs: Core.Primitive.t_u32)
    : Core.Option.t_Option Core.Primitive.t_u32 =
  Core.Option.Option_Some (unchecked_add_u32 self rhs) <: Core.Option.t_Option Core.Primitive.t_u32

let checked_add586246465 (self rhs: Core.Primitive.t_u64)
    : Core.Option.t_Option Core.Primitive.t_u64 =
  Core.Option.Option_Some (unchecked_add_u64 self rhs) <: Core.Option.t_Option Core.Primitive.t_u64

let checked_add218978451 (self rhs: Core.Primitive.t_u128)
    : Core.Option.t_Option Core.Primitive.t_u128 =
  Core.Option.Option_Some (unchecked_add_u128 self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_u128

let checked_add984013567 (self rhs: Core.Primitive.t_usize)
    : Core.Option.t_Option Core.Primitive.t_usize =
  Core.Option.Option_Some (unchecked_add_usize self rhs)
  <:
  Core.Option.t_Option Core.Primitive.t_usize

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

let wrapping_add634491935 (self rhs: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  wrapping_add_i8 self rhs

let wrapping_sub973428293 (self rhs: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  wrapping_sub_i8 self rhs

let wrapping_neg400701205 (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  wrapping_sub973428293 (Core.Convert.f_into #i8
        #Core.Primitive.t_i8
        #FStar.Tactics.Typeclasses.solve
        0y
      <:
      Core.Primitive.t_i8)
    self

let wrapping_abs400396545 (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  if
    is_negative350273175 (Core.Clone.f_clone #Core.Primitive.t_i8
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i8)
  then wrapping_neg400701205 self
  else self

let wrapping_add868559108 (self rhs: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  wrapping_add_i16 self rhs

let wrapping_sub189469152 (self rhs: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  wrapping_sub_i16 self rhs

let wrapping_neg860505723 (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  wrapping_sub189469152 (Core.Convert.f_into #i16
        #Core.Primitive.t_i16
        #FStar.Tactics.Typeclasses.solve
        0s
      <:
      Core.Primitive.t_i16)
    self

let wrapping_abs229076826 (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  if
    is_negative477067241 (Core.Clone.f_clone #Core.Primitive.t_i16
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i16)
  then wrapping_neg860505723 self
  else self

let wrapping_add475006616 (self rhs: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  wrapping_add_i32 self rhs

let wrapping_sub298337071 (self rhs: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  wrapping_sub_i32 self rhs

let wrapping_neg636433078 (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  wrapping_sub298337071 (Core.Convert.f_into #i32
        #Core.Primitive.t_i32
        #FStar.Tactics.Typeclasses.solve
        0l
      <:
      Core.Primitive.t_i32)
    self

let wrapping_abs729536875 (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  if
    is_negative1035644813 (Core.Clone.f_clone #Core.Primitive.t_i32
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i32)
  then wrapping_neg636433078 self
  else self

let wrapping_add590074241 (self rhs: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  wrapping_add_i64 self rhs

let wrapping_sub334584751 (self rhs: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  wrapping_sub_i64 self rhs

let wrapping_neg868282938 (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  wrapping_sub334584751 (Core.Convert.f_into #i64
        #Core.Primitive.t_i64
        #FStar.Tactics.Typeclasses.solve
        0L
      <:
      Core.Primitive.t_i64)
    self

let wrapping_abs285829312 (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  if
    is_negative1066124578 (Core.Clone.f_clone #Core.Primitive.t_i64
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i64)
  then wrapping_neg868282938 self
  else self

let wrapping_add251385439 (self rhs: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  wrapping_add_i128 self rhs

let wrapping_sub681598071 (self rhs: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  wrapping_sub_i128 self rhs

let wrapping_neg446546984 (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  wrapping_sub681598071 (Core.Convert.f_into #i128
        #Core.Primitive.t_i128
        #FStar.Tactics.Typeclasses.solve
        (pub_i128 0)
      <:
      Core.Primitive.t_i128)
    self

let wrapping_abs281925696 (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  if
    is_negative221698470 (Core.Clone.f_clone #Core.Primitive.t_i128
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i128)
  then wrapping_neg446546984 self
  else self

let wrapping_add226040243 (self rhs: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  wrapping_add_isize self rhs

let wrapping_sub698035192 (self rhs: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  wrapping_sub_isize self rhs

let wrapping_neg912291768 (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  wrapping_sub698035192 (Core.Convert.f_into #isize
        #Core.Primitive.t_isize
        #FStar.Tactics.Typeclasses.solve
        (isz 0)
      <:
      Core.Primitive.t_isize)
    self

let wrapping_abs347300819 (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  if
    is_negative693446369 (Core.Clone.f_clone #Core.Primitive.t_isize
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_isize)
  then wrapping_neg912291768 self
  else self

let checked_div508301931 (self rhs: Core.Primitive.t_u8) : Core.Option.t_Option Core.Primitive.t_u8 =
  if
    rhs =.
    (Core.Convert.f_into #u8 #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve 0uy
      <:
      Core.Primitive.t_u8)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u8
  else
    Core.Option.Option_Some (unchecked_div_u8 self rhs) <: Core.Option.t_Option Core.Primitive.t_u8

let overflowing_add708890057 (self rhs: Core.Primitive.t_u8) : (Core.Primitive.t_u8 & bool) =
  add_with_overflow_u8 self rhs

let checked_div614920780 (self rhs: Core.Primitive.t_u16)
    : Core.Option.t_Option Core.Primitive.t_u16 =
  if
    rhs =.
    (Core.Convert.f_into #u16 #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve 0us
      <:
      Core.Primitive.t_u16)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u16
  else
    Core.Option.Option_Some (unchecked_div_u16 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u16

let overflowing_add1023344178 (self rhs: Core.Primitive.t_u16) : (Core.Primitive.t_u16 & bool) =
  add_with_overflow_u16 self rhs

let checked_div979383477 (self rhs: Core.Primitive.t_u32)
    : Core.Option.t_Option Core.Primitive.t_u32 =
  if
    rhs =.
    (Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
      <:
      Core.Primitive.t_u32)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u32
  else
    Core.Option.Option_Some (unchecked_div_u32 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u32

let overflowing_add905744292 (self rhs: Core.Primitive.t_u32) : (Core.Primitive.t_u32 & bool) =
  add_with_overflow_u32 self rhs

let checked_div988689127 (self rhs: Core.Primitive.t_u64)
    : Core.Option.t_Option Core.Primitive.t_u64 =
  if
    rhs =.
    (Core.Convert.f_into #u64 #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve 0uL
      <:
      Core.Primitive.t_u64)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u64
  else
    Core.Option.Option_Some (unchecked_div_u64 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u64

let overflowing_add581983607 (self rhs: Core.Primitive.t_u64) : (Core.Primitive.t_u64 & bool) =
  add_with_overflow_u64 self rhs

let checked_div344106746 (self rhs: Core.Primitive.t_u128)
    : Core.Option.t_Option Core.Primitive.t_u128 =
  if
    rhs =.
    (Core.Convert.f_into #u128 #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 0)
      <:
      Core.Primitive.t_u128)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u128
  else
    Core.Option.Option_Some (unchecked_div_u128 self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_u128

let overflowing_add458293681 (self rhs: Core.Primitive.t_u128) : (Core.Primitive.t_u128 & bool) =
  add_with_overflow_u128 self rhs

let checked_div80223906 (self rhs: Core.Primitive.t_usize)
    : Core.Option.t_Option Core.Primitive.t_usize =
  if
    rhs =.
    (Core.Convert.f_into #usize #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve (sz 0)
      <:
      Core.Primitive.t_usize)
  then Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize
  else
    Core.Option.Option_Some (unchecked_div_usize self rhs)
    <:
    Core.Option.t_Option Core.Primitive.t_usize

let overflowing_add682280407 (self rhs: Core.Primitive.t_usize) : (Core.Primitive.t_usize & bool) =
  add_with_overflow_usize self rhs

let abs945505614 (self: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
  if
    is_negative350273175 (Core.Clone.f_clone #Core.Primitive.t_i8
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i8)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i8 #FStar.Tactics.Typeclasses.solve self
  else self

let abs581170970 (self: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
  if
    is_negative477067241 (Core.Clone.f_clone #Core.Primitive.t_i16
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i16)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i16 #FStar.Tactics.Typeclasses.solve self
  else self

let abs590464694 (self: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
  if
    is_negative1035644813 (Core.Clone.f_clone #Core.Primitive.t_i32
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i32)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i32 #FStar.Tactics.Typeclasses.solve self
  else self

let abs654781043 (self: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
  if
    is_negative1066124578 (Core.Clone.f_clone #Core.Primitive.t_i64
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i64)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i64 #FStar.Tactics.Typeclasses.solve self
  else self

let abs204417539 (self: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
  if
    is_negative221698470 (Core.Clone.f_clone #Core.Primitive.t_i128
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_i128)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_i128 #FStar.Tactics.Typeclasses.solve self
  else self

let abs220926056 (self: Core.Primitive.t_isize) : Core.Primitive.t_isize =
  if
    is_negative693446369 (Core.Clone.f_clone #Core.Primitive.t_isize
          #FStar.Tactics.Typeclasses.solve
          self
        <:
        Core.Primitive.t_isize)
  then Core.Ops.Arith.f_neg #Core.Primitive.t_isize #FStar.Tactics.Typeclasses.solve self
  else self

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

let wrapping_add480603777 (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  wrapping_add_u8 self rhs

let wrapping_mul885216284 (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  wrapping_mul_u8 self rhs

let wrapping_add124432709 (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  wrapping_add_u16 self rhs

let wrapping_mul14465189 (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  wrapping_mul_u16 self rhs

let wrapping_add1049665857 (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  wrapping_add_u32 self rhs

let wrapping_mul203346768 (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  wrapping_mul_u32 self rhs

let wrapping_add865565639 (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  wrapping_add_u64 self rhs

let wrapping_mul742978873 (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  wrapping_mul_u64 self rhs

let wrapping_add40844100 (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  wrapping_add_u128 self rhs

let wrapping_mul294115024 (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  wrapping_mul_u128 self rhs

let wrapping_add427637036 (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  wrapping_add_usize self rhs

let wrapping_mul680896953 (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  wrapping_mul_usize self rhs

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

let wrapping_sub403906422 (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  wrapping_sub_u8 self rhs

let wrapping_neg123212788 (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  wrapping_sub403906422 (Core.Primitive.C_u8
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U8)
      <:
      Core.Primitive.t_u8)
    self

let wrapping_sub811251034 (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  wrapping_sub_u16 self rhs

let wrapping_neg128555595 (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  wrapping_sub811251034 (Core.Primitive.C_u16
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U16)
      <:
      Core.Primitive.t_u16)
    self

let wrapping_sub708953500 (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  wrapping_sub_u32 self rhs

let wrapping_neg328220773 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  wrapping_sub708953500 (Core.Primitive.C_u32
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U32)
      <:
      Core.Primitive.t_u32)
    self

let wrapping_sub762520851 (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  wrapping_sub_u64 self rhs

let wrapping_neg617136337 (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  wrapping_sub762520851 (Core.Primitive.C_u64
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U64)
      <:
      Core.Primitive.t_u64)
    self

let wrapping_sub409310259 (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  wrapping_sub_u128 self rhs

let wrapping_neg729451428 (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  wrapping_sub409310259 (Core.Primitive.C_u128
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U128)
      <:
      Core.Primitive.t_u128)
    self

let wrapping_sub813101882 (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  wrapping_sub_usize self rhs

let wrapping_neg342773446 (self: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  wrapping_sub813101882 (Core.Primitive.C_usize
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U64)
      <:
      Core.Primitive.t_usize)
    self

let wrapping_div660080892 (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self /! rhs

let wrapping_div_euclid481233436 (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self /! rhs

let wrapping_div366977334 (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self /! rhs

let wrapping_div_euclid22267888 (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  self /! rhs

let wrapping_div931150450 (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self /! rhs

let wrapping_div_euclid606291997 (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  self /! rhs

let wrapping_div168427046 (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self /! rhs

let wrapping_div_euclid321252086 (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  self /! rhs

let wrapping_div692427683 (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self /! rhs

let wrapping_div_euclid926334515 (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  self /! rhs

let wrapping_div905768546 (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize = self /! rhs

let wrapping_div_euclid90317722 (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  self /! rhs

let wrapping_rem984569721 (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self %! rhs

let wrapping_rem_euclid946579345 (self rhs: Core.Primitive.t_u8) : Core.Primitive.t_u8 = self %! rhs

let wrapping_rem378598035 (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 = self %! rhs

let wrapping_rem_euclid602402638 (self rhs: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  self %! rhs

let wrapping_rem292009099 (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 = self %! rhs

let wrapping_rem_euclid1020271291 (self rhs: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  self %! rhs

let wrapping_rem390602260 (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 = self %! rhs

let wrapping_rem_euclid839264546 (self rhs: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  self %! rhs

let wrapping_rem332379920 (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 = self %! rhs

let wrapping_rem_euclid646122423 (self rhs: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  self %! rhs

let wrapping_rem333089373 (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize = self %! rhs

let wrapping_rem_euclid769656504 (self rhs: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  self %! rhs

let bswap_u8 (x: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  let (count: Core.Primitive.t_u8):Core.Primitive.t_u8 =
    Core.Convert.f_into #u8 #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve 0uy
  in
  let count:Core.Primitive.t_u8 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS690311813
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

let ctpop_u8 (x: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS690311813
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
          v_BITS690311813
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

let count_ones202509899 (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 = ctpop_u8 self

let swap_bytes657156997 (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 =
  Core.Convert.f_into #Core.Primitive.t_u8
    #Core.Primitive.t_u8
    #FStar.Tactics.Typeclasses.solve
    (bswap_u8 self <: Core.Primitive.t_u8)

let from_be746282521 (x: Core.Primitive.t_u8) : Core.Primitive.t_u8 = swap_bytes657156997 x

let to_be972448780 (self: Core.Primitive.t_u8) : Core.Primitive.t_u8 = swap_bytes657156997 self

let trailing_zeros572929871 (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 = cttz_u8 self

let bswap_u16 (x: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  let (count: Core.Primitive.t_u16):Core.Primitive.t_u16 =
    Core.Convert.f_into #u16 #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve 0us
  in
  let count:Core.Primitive.t_u16 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS277333551
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

let ctpop_u16 (x: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS277333551
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
          v_BITS277333551
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

let count_ones91875752 (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 = ctpop_u16 self

let swap_bytes926722059 (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 =
  Core.Convert.f_into #Core.Primitive.t_u16
    #Core.Primitive.t_u16
    #FStar.Tactics.Typeclasses.solve
    (bswap_u16 self <: Core.Primitive.t_u16)

let from_be510959665 (x: Core.Primitive.t_u16) : Core.Primitive.t_u16 = swap_bytes926722059 x

let to_be551590602 (self: Core.Primitive.t_u16) : Core.Primitive.t_u16 = swap_bytes926722059 self

let trailing_zeros421474733 (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 = cttz_u16 self

let bswap_u32 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS473478051
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

let ctpop_u32 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS473478051
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
          v_BITS473478051
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

let count_ones776185738 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 = ctpop_u32 self

let swap_bytes320480126 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  Core.Convert.f_into #Core.Primitive.t_u32
    #Core.Primitive.t_u32
    #FStar.Tactics.Typeclasses.solve
    (bswap_u32 self <: Core.Primitive.t_u32)

let from_be664756649 (x: Core.Primitive.t_u32) : Core.Primitive.t_u32 = swap_bytes320480126 x

let to_be82825962 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 = swap_bytes320480126 self

let trailing_zeros1061560720 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 = cttz_u32 self

let bswap_u64 (x: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  let (count: Core.Primitive.t_u64):Core.Primitive.t_u64 =
    Core.Convert.f_into #u64 #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve 0uL
  in
  let count:Core.Primitive.t_u64 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS177666292
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

let ctpop_u64 (x: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS177666292
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
          v_BITS177666292
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

let count_ones235885653 (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 = ctpop_u64 self

let swap_bytes722254271 (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 =
  Core.Convert.f_into #Core.Primitive.t_u64
    #Core.Primitive.t_u64
    #FStar.Tactics.Typeclasses.solve
    (bswap_u64 self <: Core.Primitive.t_u64)

let from_be16013635 (x: Core.Primitive.t_u64) : Core.Primitive.t_u64 = swap_bytes722254271 x

let to_be376714729 (self: Core.Primitive.t_u64) : Core.Primitive.t_u64 = swap_bytes722254271 self

let trailing_zeros188346231 (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 = cttz_u64 self

let bswap_u128 (x: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  let (count: Core.Primitive.t_u128):Core.Primitive.t_u128 =
    Core.Convert.f_into #u128 #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 0)
  in
  let count:Core.Primitive.t_u128 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS136999051
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

let ctpop_u128 (x: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS136999051
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
          v_BITS136999051
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

let count_ones926736261 (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 = ctpop_u128 self

let swap_bytes420879368 (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 =
  Core.Convert.f_into #Core.Primitive.t_u128
    #Core.Primitive.t_u128
    #FStar.Tactics.Typeclasses.solve
    (bswap_u128 self <: Core.Primitive.t_u128)

let from_be191085771 (x: Core.Primitive.t_u128) : Core.Primitive.t_u128 = swap_bytes420879368 x

let to_be555075987 (self: Core.Primitive.t_u128) : Core.Primitive.t_u128 = swap_bytes420879368 self

let trailing_zeros821715250 (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 = cttz_u128 self

let bswap_usize (x: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  let (count: Core.Primitive.t_usize):Core.Primitive.t_usize =
    Core.Convert.f_into #usize #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve (sz 0)
  in
  let count:Core.Primitive.t_usize =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS229952196
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

let ctpop_usize (x: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  let (count: Core.Primitive.t_u32):Core.Primitive.t_u32 =
    Core.Convert.f_into #u32 #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve 0ul
  in
  let count:Core.Primitive.t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #Core.Primitive.t_u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          v_BITS229952196
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
          v_BITS229952196
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

let count_ones441645762 (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 = ctpop_usize self

let swap_bytes268673424 (self: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  Core.Convert.f_into #Core.Primitive.t_usize
    #Core.Primitive.t_usize
    #FStar.Tactics.Typeclasses.solve
    (bswap_usize self <: Core.Primitive.t_usize)

let from_be607978059 (x: Core.Primitive.t_usize) : Core.Primitive.t_usize = swap_bytes268673424 x

let to_be561847134 (self: Core.Primitive.t_usize) : Core.Primitive.t_usize =
  swap_bytes268673424 self

let trailing_zeros42066260 (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 = cttz_usize self

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
          v_BITS136999051
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
                    (v_BITS136999051 -!
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
          v_BITS277333551
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
                    (v_BITS277333551 -!
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
          v_BITS473478051
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
                    (v_BITS473478051 -!
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
          v_BITS177666292
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
                    (v_BITS177666292 -!
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
          v_BITS690311813
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
                    (v_BITS690311813 -!
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
          v_BITS229952196
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
                    (v_BITS229952196 -!
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

let rotate_left_u128 (x: Core.Primitive.t_u128) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS136999051 in
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
    (v_BITS136999051 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u16 (x: Core.Primitive.t_u16) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u16 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS277333551 in
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
    (v_BITS277333551 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u32 (x shift: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS473478051 in
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
    (v_BITS473478051 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u64 (x: Core.Primitive.t_u64) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u64 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS177666292 in
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
    (v_BITS177666292 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_u8 (x: Core.Primitive.t_u8) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u8 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS690311813 in
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
    (v_BITS690311813 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_left_usize (x: Core.Primitive.t_usize) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_usize =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS229952196 in
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
    (v_BITS229952196 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u128 (x: Core.Primitive.t_u128) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS136999051 in
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
    (v_BITS136999051 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u16 (x: Core.Primitive.t_u16) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u16 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS277333551 in
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
    (v_BITS277333551 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u32 (x shift: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS473478051 in
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
    (v_BITS473478051 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u64 (x: Core.Primitive.t_u64) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u64 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS177666292 in
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
    (v_BITS177666292 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_u8 (x: Core.Primitive.t_u8) (shift: Core.Primitive.t_u32) : Core.Primitive.t_u8 =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS690311813 in
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
    (v_BITS690311813 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let rotate_right_usize (x: Core.Primitive.t_usize) (shift: Core.Primitive.t_u32)
    : Core.Primitive.t_usize =
  let (shift: Core.Primitive.t_u32):Core.Primitive.t_u32 = shift %! v_BITS229952196 in
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
    (v_BITS229952196 -!
      (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve shift
        <:
        Core.Primitive.t_u32)
      <:
      Core.Primitive.t_u32)
  in
  left |. right

let leading_zeros75047366 (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 = ctlz_u8 self

let rotate_left792925914 (self: Core.Primitive.t_u8) (n: Core.Primitive.t_u32) : Core.Primitive.t_u8 =
  rotate_left_u8 self n

let rotate_right166090082 (self: Core.Primitive.t_u8) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u8 = rotate_right_u8 self n

let leading_zeros462412478 (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 = ctlz_u16 self

let rotate_left297034175 (self: Core.Primitive.t_u16) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u16 = rotate_left_u16 self n

let rotate_right138522246 (self: Core.Primitive.t_u16) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u16 = rotate_right_u16 self n

let leading_zeros698221972 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 = ctlz_u32 self

let rotate_left823573251 (self n: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  rotate_left_u32 self n

let rotate_right869195717 (self n: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  rotate_right_u32 self n

let leading_zeros338302110 (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 = ctlz_u64 self

let rotate_left618936072 (self: Core.Primitive.t_u64) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u64 = rotate_left_u64 self n

let rotate_right1041614027 (self: Core.Primitive.t_u64) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u64 = rotate_right_u64 self n

let leading_zeros19644612 (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 = ctlz_u128 self

let rotate_left1065866885 (self: Core.Primitive.t_u128) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 = rotate_left_u128 self n

let rotate_right591112338 (self: Core.Primitive.t_u128) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_u128 = rotate_right_u128 self n

let leading_zeros905233489 (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 = ctlz_usize self

let rotate_left996672710 (self: Core.Primitive.t_usize) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_usize = rotate_left_usize self n

let rotate_right442734174 (self: Core.Primitive.t_usize) (n: Core.Primitive.t_u32)
    : Core.Primitive.t_usize = rotate_right_usize self n

let rem_euclid622298453 (self rhs: Core.Primitive.t_i8) : Core.Primitive.t_i8 =
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
  then wrapping_add634491935 r (wrapping_abs400396545 rhs <: Core.Primitive.t_i8)
  else r

let rem_euclid158017644 (self rhs: Core.Primitive.t_i16) : Core.Primitive.t_i16 =
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
  then wrapping_add868559108 r (wrapping_abs229076826 rhs <: Core.Primitive.t_i16)
  else r

let rem_euclid881249982 (self rhs: Core.Primitive.t_i32) : Core.Primitive.t_i32 =
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
  then wrapping_add475006616 r (wrapping_abs729536875 rhs <: Core.Primitive.t_i32)
  else r

let rem_euclid1057082210 (self rhs: Core.Primitive.t_i64) : Core.Primitive.t_i64 =
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
  then wrapping_add590074241 r (wrapping_abs285829312 rhs <: Core.Primitive.t_i64)
  else r

let rem_euclid254910751 (self rhs: Core.Primitive.t_i128) : Core.Primitive.t_i128 =
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
  then wrapping_add251385439 r (wrapping_abs281925696 rhs <: Core.Primitive.t_i128)
  else r

let rem_euclid828379367 (self rhs: Core.Primitive.t_isize) : Core.Primitive.t_isize =
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
  then wrapping_add226040243 r (wrapping_abs347300819 rhs <: Core.Primitive.t_isize)
  else r

let count_zeros558337492 (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  count_ones202509899 (~.self <: Core.Primitive.t_u8)

let leading_ones55148479 (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  leading_zeros75047366 (~.self <: Core.Primitive.t_u8)

let trailing_ones359778731 (self: Core.Primitive.t_u8) : Core.Primitive.t_u32 =
  trailing_zeros572929871 (~.self <: Core.Primitive.t_u8)

let count_zeros199825317 (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  count_ones91875752 (~.self <: Core.Primitive.t_u16)

let leading_ones164277656 (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  leading_zeros462412478 (~.self <: Core.Primitive.t_u16)

let trailing_ones903944727 (self: Core.Primitive.t_u16) : Core.Primitive.t_u32 =
  trailing_zeros421474733 (~.self <: Core.Primitive.t_u16)

let count_zeros942566041 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  count_ones776185738 (~.self <: Core.Primitive.t_u32)

let leading_ones766486760 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  leading_zeros698221972 (~.self <: Core.Primitive.t_u32)

let trailing_ones223371510 (self: Core.Primitive.t_u32) : Core.Primitive.t_u32 =
  trailing_zeros1061560720 (~.self <: Core.Primitive.t_u32)

let count_zeros60346158 (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  count_ones235885653 (~.self <: Core.Primitive.t_u64)

let leading_ones404666910 (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  leading_zeros338302110 (~.self <: Core.Primitive.t_u64)

let trailing_ones601201120 (self: Core.Primitive.t_u64) : Core.Primitive.t_u32 =
  trailing_zeros188346231 (~.self <: Core.Primitive.t_u64)

let count_zeros824862815 (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  count_ones926736261 (~.self <: Core.Primitive.t_u128)

let leading_ones475503572 (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  leading_zeros19644612 (~.self <: Core.Primitive.t_u128)

let trailing_ones705845381 (self: Core.Primitive.t_u128) : Core.Primitive.t_u32 =
  trailing_zeros821715250 (~.self <: Core.Primitive.t_u128)

let count_zeros73479642 (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  count_ones441645762 (~.self <: Core.Primitive.t_usize)

let leading_ones667660708 (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  leading_zeros905233489 (~.self <: Core.Primitive.t_usize)

let trailing_ones979548463 (self: Core.Primitive.t_usize) : Core.Primitive.t_u32 =
  trailing_zeros42066260 (~.self <: Core.Primitive.t_usize)
