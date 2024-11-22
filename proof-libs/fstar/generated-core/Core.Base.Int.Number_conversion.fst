module Core.Base.Int.Number_conversion
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Core.Primitive
open Core.Cmp
open Core.Ops.Arith

let rec impl__from_u128_binary (x: u128 {match x with | C_u128 v -> v.f_v > 0}) : Tot Core.Base.Int.t_Positive (decreases (match x with | C_u128 n -> n.f_v <: nat)) =  match x with | C_u128 x -> x.f_v
  // if Core.Cmp.f_eq x (pub_u128 1)
  // then Core.Base.Int.Base_spec.impl_8__xH
  // else
  //   if Core.Cmp.f_eq (f_rem x (pub_u128 2) <: u128) (pub_u128 0)
  //   then
  //     let _ = assume ((match (f_div x (pub_u128 2) <: u128) with | C_u128 n -> n.f_v) < (match x with | C_u128 n -> n.f_v)) in
  //     Core.Base.Int.Base_spec.impl_8__xO (impl__from_u128_binary (Core.Ops.Arith.f_div x
  //               (pub_u128 2)
  //             <:
  //             u128)
  //         <:
  //         Core.Base.Int.t_Positive)
  //   else
  //     Core.Base.Int.Base_spec.impl_8__xI (impl__from_u128_binary (Core.Ops.Arith.f_div x
  //               (pub_u128 2)
  //             <:
  //             u128)
  //         <:
  //         Core.Base.Int.t_Positive)

// let rec impl__from_u16_binary (x: u16) : Tot Core.Base.Int.t_Positive (decreases (match x with | C_u16 n -> n.f_v <: nat)) =
//   if Core.Cmp.f_eq x (pub_u16 1)
//   then Core.Base.Int.Base_spec.impl_8__xH
//   else
//     if Core.Cmp.f_eq  (Core.Ops.Arith.f_rem x (pub_u16 2) <: u16) (pub_u16 0)
//     then
//       let _ = assume ((match (f_div x (pub_u16 2) <: u16) with | C_u16 n -> n.f_v) < (match x with | C_u16 n -> n.f_v)) in
//       Core.Base.Int.Base_spec.impl_8__xO (impl__from_u16_binary (Core.Ops.Arith.f_div x (pub_u16 2)
//               <:
//               u16)
//           <:
//           Core.Base.Int.t_Positive)
//     else
//       Core.Base.Int.Base_spec.impl_8__xI (impl__from_u16_binary (Core.Ops.Arith.f_div x (pub_u16 2)
//               <:
//               u16)
//           <:
//           Core.Base.Int.t_Positive)

// let rec impl__from_u32_binary (x: u32) : Tot Core.Base.Int.t_Positive (decreases (match x with | C_u32 n -> n.f_v <: nat)) =
//   if Core.Cmp.f_eq x (pub_u32 1)
//   then Core.Base.Int.Base_spec.impl_8__xH
//   else
//     if Core.Cmp.f_eq (Core.Ops.Arith.f_rem x (pub_u32 2) <: u32) (pub_u32 0)
//     then
//       let _ = assume ((match (f_div x (pub_u32 2) <: u32) with | C_u32 n -> n.f_v) < (match x with | C_u32 n -> n.f_v)) in
//       Core.Base.Int.Base_spec.impl_8__xO (impl__from_u32_binary (Core.Ops.Arith.f_div x (pub_u32 2)
//               <:
//               u32)
//           <:
//           Core.Base.Int.t_Positive)
//     else
//       Core.Base.Int.Base_spec.impl_8__xI (impl__from_u32_binary (Core.Ops.Arith.f_div x (pub_u32 2)
//               <:
//               u32)
//           <:
//           Core.Base.Int.t_Positive)

// let rec impl__from_u64_binary (x: u64) : Tot Core.Base.Int.t_Positive (decreases (match x with | C_u64 n -> n.f_v <: nat)) =
//   if Core.Cmp.f_eq x (pub_u64 1)
//   then Core.Base.Int.Base_spec.impl_8__xH
//   else
//     if Core.Cmp.f_eq (Core.Ops.Arith.f_rem x (pub_u64 2) <: u64) (pub_u64 0)
//     then
//       let _ = assume ((match (f_div x (pub_u64 2) <: u64) with | C_u64 n -> n.f_v) < (match x with | C_u64 n -> n.f_v)) in
//       Core.Base.Int.Base_spec.impl_8__xO (impl__from_u64_binary (Core.Ops.Arith.f_div x (pub_u64 2)
//               <:
//               u64)
//           <:
//           Core.Base.Int.t_Positive)
//     else
//       Core.Base.Int.Base_spec.impl_8__xI (impl__from_u64_binary (Core.Ops.Arith.f_div x (pub_u64 2)
//               <:
//               u64)
//           <:
//           Core.Base.Int.t_Positive)


// let rec impl__from_u8_binary (x: u8) : Tot Core.Base.Int.t_Positive (decreases (match x with | C_u8 n -> n.f_v <: nat)) =
//   if Core.Cmp.f_eq x (pub_u8 1)
//   then Core.Base.Int.Base_spec.impl_8__xH
//   else
//     if Core.Cmp.f_eq (Core.Ops.Arith.f_rem x (pub_u8 2) <: u8) (pub_u8 0)
//     then
//       let _ = assume ((match (f_div x (pub_u8 2) <: u8) with | C_u8 n -> n.f_v) < (match x with | C_u8 n -> n.f_v)) in
//       Core.Base.Int.Base_spec.impl_8__xO (impl__from_u8_binary (Core.Ops.Arith.f_div x (pub_u8 2)
//               <:
//               u8)
//           <:
//           Core.Base.Int.t_Positive)
//     else
//       Core.Base.Int.Base_spec.impl_8__xI (impl__from_u8_binary (Core.Ops.Arith.f_div x (pub_u8 2)
//               <:
//               u8)
//           <:
//           Core.Base.Int.t_Positive)

let rec impl__from_usize_binary (x: usize {match x with | C_usize v -> v.f_v > 0}) : Tot Core.Base.Int.t_Positive (decreases (match x with | C_usize n -> n.f_v <: nat)) =  match x with | C_usize v -> v.f_v
  // if Core.Cmp.f_eq x (sz 1)
  // then Core.Base.Int.Base_spec.impl_8__xH
  // else
  //   if Core.Cmp.f_eq (Core.Ops.Arith.f_rem x (sz 2) <: usize) (sz 0)
  //   then
  //     let _ = assume ((match (f_div x (sz 2) <: usize) with | C_usize n -> n.f_v) < (match x with | C_usize n -> n.f_v)) in
  //     Core.Base.Int.Base_spec.impl_8__xO (impl__from_usize_binary (Core.Ops.Arith.f_div x (sz 2)
  //             <:
  //             usize)
  //         <:
  //         Core.Base.Int.t_Positive)
  //   else
  //     Core.Base.Int.Base_spec.impl_8__xI (impl__from_usize_binary (Core.Ops.Arith.f_div x (sz 2)
  //             <:
  //             usize)
  //         <:
  //         Core.Base.Int.t_Positive)

let rec impl__to_u128_binary (self: Core.Base.Int.t_Positive) : u128 =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  -> pub_u128 1
  | Core.Base.Int.POSITIVE_XO p ->
    Core.Ops.Arith.f_mul (impl__to_u128_binary p <: u128) (pub_u128 2)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Ops.Arith.f_add (Core.Ops.Arith.f_mul (impl__to_u128_binary p <: u128) (pub_u128 2)
        <:
        u128)
      (pub_u128 1)

let rec impl__to_u16_binary (self: Core.Base.Int.t_Positive) : u16 =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  -> pub_u16 1
  | Core.Base.Int.POSITIVE_XO p -> Core.Ops.Arith.f_mul (impl__to_u16_binary p <: u16) (pub_u16 2)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Ops.Arith.f_add (Core.Ops.Arith.f_mul (impl__to_u16_binary p <: u16) (pub_u16 2) <: u16) (pub_u16 1)

let rec impl__to_u32_binary (self: Core.Base.Int.t_Positive) : u32 =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  -> pub_u32 1
  | Core.Base.Int.POSITIVE_XO p -> Core.Ops.Arith.f_mul (impl__to_u32_binary p <: u32) (pub_u32 2)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Ops.Arith.f_add (Core.Ops.Arith.f_mul (impl__to_u32_binary p <: u32) (pub_u32 2) <: u32) (pub_u32 1)

let rec impl__to_u64_binary (self: Core.Base.Int.t_Positive) : u64 =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  -> pub_u64 1
  | Core.Base.Int.POSITIVE_XO p -> Core.Ops.Arith.f_mul (impl__to_u64_binary p <: u64) (pub_u64 2)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Ops.Arith.f_add (Core.Ops.Arith.f_mul (impl__to_u64_binary p <: u64) (pub_u64 2) <: u64) (pub_u64 1)

let rec impl__to_u8_binary (self: Core.Base.Int.t_Positive) : u8 =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  -> pub_u8 1
  | Core.Base.Int.POSITIVE_XO p -> Core.Ops.Arith.f_mul (impl__to_u8_binary p <: u8) (pub_u8 2)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Ops.Arith.f_add (Core.Ops.Arith.f_mul (impl__to_u8_binary p <: u8) (pub_u8 2) <: u8) (pub_u8 1)

let rec impl__to_usize_binary (self: Core.Base.Int.t_Positive) : usize =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  -> sz 1
  | Core.Base.Int.POSITIVE_XO p ->
    Core.Ops.Arith.f_mul (impl__to_usize_binary p <: usize) (sz 2)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Ops.Arith.f_add (Core.Ops.Arith.f_mul (impl__to_usize_binary p <: usize) (sz 2)
        <:
        usize)
      (sz 1)

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_1: Core.Convert.t_From Core.Base.Int.t_HaxInt u8 =
//   {
//     f_from_pre = (fun (x: u8) -> true);
//     f_from_post = (fun (x: u8) (out: Core.Base.Int.t_HaxInt) -> true);
//     f_from
//     =
//     fun (x: u8) ->
//       if Core.Cmp.f_eq x (pub_u8 0)
//       then Core.Base.Int.Base_spec.impl_9__ZERO
//       else
//         Core.Base.Int.Base_spec.impl_4__to_int (impl__from_u8_binary x <: Core.Base.Int.t_Positive)
//   }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From u8 Core.Base.Int.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Int.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Int.t_HaxInt) (out: u8) -> true);
    f_from
    =
    fun (x: Core.Base.Int.t_HaxInt) ->
      match Core.Base.Int.Base_spec.impl_9__match_pos x with
      | Core.Base.Int.POS_ZERO  -> pub_u8 0
      | Core.Base.Int.POS_POS p -> impl__to_u8_binary p
  }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_3: Core.Convert.t_From Core.Base.Int.t_HaxInt u16 =
//   {
//     f_from_pre = (fun (x: u16) -> true);
//     f_from_post = (fun (x: u16) (out: Core.Base.Int.t_HaxInt) -> true);
//     f_from
//     =
//     fun (x: u16) ->
//       if Core.Cmp.f_eq x (pub_u16 0)
//       then Core.Base.Int.Base_spec.impl_9__ZERO
//       else
//         Core.Base.Int.Base_spec.impl_4__to_int (impl__from_u16_binary x <: Core.Base.Int.t_Positive)
//   }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From u16 Core.Base.Int.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Int.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Int.t_HaxInt) (out: u16) -> true);
    f_from
    =
    fun (x: Core.Base.Int.t_HaxInt) ->
      match Core.Base.Int.Base_spec.impl_9__match_pos x with
      | Core.Base.Int.POS_ZERO  -> pub_u16 0
      | Core.Base.Int.POS_POS p -> impl__to_u16_binary p
  }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_5: Core.Convert.t_From Core.Base.Int.t_HaxInt u32 =
//   {
//     f_from_pre = (fun (x: u32) -> true);
//     f_from_post = (fun (x: u32) (out: Core.Base.Int.t_HaxInt) -> true);
//     f_from
//     =
//     fun (x: u32) ->
//       if Core.Cmp.f_eq x (pub_u32 0)
//       then Core.Base.Int.Base_spec.impl_9__ZERO
//       else
//         Core.Base.Int.Base_spec.impl_4__to_int (impl__from_u32_binary x <: Core.Base.Int.t_Positive)
//   }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From u32 Core.Base.Int.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Int.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Int.t_HaxInt) (out: u32) -> true);
    f_from
    =
    fun (x: Core.Base.Int.t_HaxInt) ->
      match Core.Base.Int.Base_spec.impl_9__match_pos x with
      | Core.Base.Int.POS_ZERO  -> pub_u32 0
      | Core.Base.Int.POS_POS p -> impl__to_u32_binary p
  }

// [@@ FStar.Tactics.Typeclasses.tcinstance]
// let impl_7: Core.Convert.t_From Core.Base.Int.t_HaxInt u64 =
//   {
//     f_from_pre = (fun (x: u64) -> true);
//     f_from_post = (fun (x: u64) (out: Core.Base.Int.t_HaxInt) -> true);
//     f_from
//     =
//     fun (x: u64) ->
//       if Core.Cmp.f_eq x (pub_u64 0)
//       then Core.Base.Int.Base_spec.impl_9__ZERO
//       else
//         Core.Base.Int.Base_spec.impl_4__to_int (impl__from_u64_binary x <: Core.Base.Int.t_Positive)
//   }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From u64 Core.Base.Int.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Int.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Int.t_HaxInt) (out: u64) -> true);
    f_from
    =
    fun (x: Core.Base.Int.t_HaxInt) ->
      match Core.Base.Int.Base_spec.impl_9__match_pos x with
      | Core.Base.Int.POS_ZERO  -> pub_u64 0
      | Core.Base.Int.POS_POS p -> impl__to_u64_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From Core.Base.Int.t_HaxInt u128 =
  {
    f_from_pre = (fun (x: u128) -> true);
    f_from_post = (fun (x: u128) (out: Core.Base.Int.t_HaxInt) -> true);
    f_from
    =
    fun (x: u128) ->
      if Core.Cmp.f_eq x (pub_u128 0)
      then Core.Base.Int.Base_spec.impl_9__ZERO
      else
        Core.Base.Int.Base_spec.impl_4__to_int (impl__from_u128_binary x <: Core.Base.Int.t_Positive
          )
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From u128 Core.Base.Int.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Int.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Int.t_HaxInt) (out: u128) -> true);
    f_from
    =
    fun (x: Core.Base.Int.t_HaxInt) ->
      match Core.Base.Int.Base_spec.impl_9__match_pos x with
      | Core.Base.Int.POS_ZERO  -> pub_u128 0
      | Core.Base.Int.POS_POS p -> impl__to_u128_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From Core.Base.Int.t_HaxInt usize =
  {
    f_from_pre = (fun (x: usize) -> true);
    f_from_post = (fun (x: usize) (out: Core.Base.Int.t_HaxInt) -> true);
    f_from
    =
    fun (x: usize) ->
      if Core.Cmp.f_eq x (sz 0)
      then Core.Base.Int.Base_spec.impl_9__ZERO
      else
        Core.Base.Int.Base_spec.impl_4__to_int (impl__from_usize_binary x
            <:
            Core.Base.Int.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From usize Core.Base.Int.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Int.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Int.t_HaxInt) (out: usize) -> true);
    f_from
    =
    fun (x: Core.Base.Int.t_HaxInt) ->
      match Core.Base.Int.Base_spec.impl_9__match_pos x with
      | Core.Base.Int.POS_ZERO  -> sz 0
      | Core.Base.Int.POS_POS p -> impl__to_usize_binary p
  }
