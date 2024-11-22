module Core.Base.Number_conversion
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rec impl_24__from_u128_binary (x: u128)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U128.ne x (pub_u128 0))
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U128.eq x (pub_u128 1)
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U128.eq (Rust_primitives.U128.rem x (pub_u128 2) <: u128) (pub_u128 0)
    then
      Core.Base.Spec.Binary.Positive.xO (impl_24__from_u128_binary (Rust_primitives.U128.div x
                (pub_u128 2)
              <:
              u128)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (impl_24__from_u128_binary (Rust_primitives.U128.div x
                (pub_u128 2)
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
        Core.Base.Spec.Binary.Positive.positive_to_int (impl_24__from_u128_binary x
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
        Core.Base.Spec.Z.Z_NEG
        (impl_24__from_u128_binary (Core.Num.impl__i128__unsigned_abs x <: u128))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS
        (impl_24__from_u128_binary (Core.Num.impl__i128__unsigned_abs x <: u128))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec impl_24__from_u16_binary (x: u16)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U16.ne x 0us)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U16.eq x 1us
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U16.eq (Rust_primitives.U16.rem x 2us <: u16) 0us
    then
      Core.Base.Spec.Binary.Positive.xO (impl_24__from_u16_binary (Rust_primitives.U16.div x 2us
              <:
              u16)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (impl_24__from_u16_binary (Rust_primitives.U16.div x 2us
              <:
              u16)
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
        Core.Base.Spec.Binary.Positive.positive_to_int (impl_24__from_u16_binary x
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
        Core.Base.Spec.Z.Z_NEG
        (impl_24__from_u16_binary (Core.Num.impl__i16__unsigned_abs x <: u16))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS
        (impl_24__from_u16_binary (Core.Num.impl__i16__unsigned_abs x <: u16))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec impl_24__from_u32_binary (x: u32)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U32.ne x 0ul)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U32.eq x 1ul
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U32.eq (Rust_primitives.U32.rem x 2ul <: u32) 0ul
    then
      Core.Base.Spec.Binary.Positive.xO (impl_24__from_u32_binary (Rust_primitives.U32.div x 2ul
              <:
              u32)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (impl_24__from_u32_binary (Rust_primitives.U32.div x 2ul
              <:
              u32)
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
        Core.Base.Spec.Binary.Positive.positive_to_int (impl_24__from_u32_binary x
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
        Core.Base.Spec.Z.Z_NEG
        (impl_24__from_u32_binary (Core.Num.impl__i32__unsigned_abs x <: u32))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS
        (impl_24__from_u32_binary (Core.Num.impl__i32__unsigned_abs x <: u32))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec impl_24__from_u64_binary (x: u64)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U64.ne x 0uL)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U64.eq x 1uL
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U64.eq (Rust_primitives.U64.rem x 2uL <: u64) 0uL
    then
      Core.Base.Spec.Binary.Positive.xO (impl_24__from_u64_binary (Rust_primitives.U64.div x 2uL
              <:
              u64)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (impl_24__from_u64_binary (Rust_primitives.U64.div x 2uL
              <:
              u64)
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
        Core.Base.Spec.Binary.Positive.positive_to_int (impl_24__from_u64_binary x
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
        Core.Base.Spec.Z.Z_NEG
        (impl_24__from_u64_binary (Core.Num.impl__i64__unsigned_abs x <: u64))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS
        (impl_24__from_u64_binary (Core.Num.impl__i64__unsigned_abs x <: u64))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec impl_24__from_u8_binary (x: u8)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U8.ne x 0uy)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U8.eq x 1uy
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U8.eq (Rust_primitives.U8.rem x 2uy <: u8) 0uy
    then
      Core.Base.Spec.Binary.Positive.xO (impl_24__from_u8_binary (Rust_primitives.U8.div x 2uy <: u8
            )
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (impl_24__from_u8_binary (Rust_primitives.U8.div x 2uy <: u8
            )
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
        Core.Base.Spec.Binary.Positive.positive_to_int (impl_24__from_u8_binary x
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
        Core.Base.Spec.Z.Z_NEG (impl_24__from_u8_binary (Core.Num.impl__i8__unsigned_abs x <: u8))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (impl_24__from_u8_binary (Core.Num.impl__i8__unsigned_abs x <: u8))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec impl_24__from_usize_binary (x: usize)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.Usize.ne x (sz 0))
      (fun _ -> Prims.l_True) =
  if Rust_primitives.Usize.eq x (sz 1)
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.Usize.eq (Rust_primitives.Usize.rem x (sz 2) <: usize) (sz 0)
    then
      Core.Base.Spec.Binary.Positive.xO (impl_24__from_usize_binary (Rust_primitives.Usize.div x
                (sz 2)
              <:
              usize)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (impl_24__from_usize_binary (Rust_primitives.Usize.div x
                (sz 2)
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
        Core.Base.Spec.Binary.Positive.positive_to_int (impl_24__from_usize_binary x
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
        Core.Base.Spec.Z.Z_NEG
        (impl_24__from_usize_binary (Core.Num.impl__isize__unsigned_abs x <: usize))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS
        (impl_24__from_usize_binary (Core.Num.impl__isize__unsigned_abs x <: usize))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec impl_24__to_u128_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u128 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> pub_u128 1
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U128.mul (impl_24__to_u128_binary p <: u128) (pub_u128 2)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U128.add (Rust_primitives.U128.mul (impl_24__to_u128_binary p <: u128)
          (pub_u128 2)
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
      | Core.Base.Spec.Binary.Pos.POS_POS p -> impl_24__to_u128_binary p
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
        Rust_primitives.I128.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U128.sub (impl_24__to_u128_binary
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
      | Core.Base.Spec.Z.Z_POS x -> cast (impl_24__to_u128_binary x <: u128) <: i128
  }

let rec impl_24__to_u16_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u16 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1us
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U16.mul (impl_24__to_u16_binary p <: u16) 2us
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U16.add (Rust_primitives.U16.mul (impl_24__to_u16_binary p <: u16) 2us <: u16)
      1us

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
      | Core.Base.Spec.Binary.Pos.POS_POS p -> impl_24__to_u16_binary p
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
        Rust_primitives.I16.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U16.sub (impl_24__to_u16_binary
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
      | Core.Base.Spec.Z.Z_POS x -> cast (impl_24__to_u16_binary x <: u16) <: i16
  }

let rec impl_24__to_u32_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u32 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1ul
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U32.mul (impl_24__to_u32_binary p <: u32) 2ul
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U32.add (Rust_primitives.U32.mul (impl_24__to_u32_binary p <: u32) 2ul <: u32)
      1ul

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
      | Core.Base.Spec.Binary.Pos.POS_POS p -> impl_24__to_u32_binary p
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
        Rust_primitives.I32.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U32.sub (impl_24__to_u32_binary
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
      | Core.Base.Spec.Z.Z_POS x -> cast (impl_24__to_u32_binary x <: u32) <: i32
  }

let rec impl_24__to_u64_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u64 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1uL
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U64.mul (impl_24__to_u64_binary p <: u64) 2uL
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U64.add (Rust_primitives.U64.mul (impl_24__to_u64_binary p <: u64) 2uL <: u64)
      1uL

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
      | Core.Base.Spec.Binary.Pos.POS_POS p -> impl_24__to_u64_binary p
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
        Rust_primitives.I64.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U64.sub (impl_24__to_u64_binary
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
      | Core.Base.Spec.Z.Z_POS x -> cast (impl_24__to_u64_binary x <: u64) <: i64
  }

let rec impl_24__to_u8_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u8 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1uy
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U8.mul (impl_24__to_u8_binary p <: u8) 2uy
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U8.add (Rust_primitives.U8.mul (impl_24__to_u8_binary p <: u8) 2uy <: u8) 1uy

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
      | Core.Base.Spec.Binary.Pos.POS_POS p -> impl_24__to_u8_binary p
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
        Rust_primitives.I8.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U8.sub (impl_24__to_u8_binary
                          x
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
      | Core.Base.Spec.Z.Z_POS x -> cast (impl_24__to_u8_binary x <: u8) <: i8
  }

let rec impl_24__to_usize_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : usize =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> sz 1
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.Usize.mul (impl_24__to_usize_binary p <: usize) (sz 2)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.Usize.add (Rust_primitives.Usize.mul (impl_24__to_usize_binary p <: usize)
          (sz 2)
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
      | Core.Base.Spec.Binary.Pos.POS_POS p -> impl_24__to_usize_binary p
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
        Rust_primitives.Isize.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.Usize.sub (impl_24__to_usize_binary
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
      | Core.Base.Spec.Z.Z_POS x -> cast (impl_24__to_usize_binary x <: usize) <: isize
  }
