module Barrett
#set-options "--fuel 0 --ifuel 1 --z3rlimit 250"
open Core
open FStar.Mul

unfold
let t_FieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_SHIFT: i64 = 26L

let v_FIELD_MODULUS: i32 = 3329l

let v_BARRETT_R: i64 = 1L <<! v_BARRETT_SHIFT

let barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        (Core.Convert.f_from value <: i64) >. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from value <: i64) <. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg v_FIELD_MODULUS <: i32) && result <. v_FIELD_MODULUS) =
  let t:i64 = (Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER in
  let t:i64 = t +! (v_BARRETT_R >>! 1l <: i64) in
  let quotient:i64 = t >>! v_BARRETT_SHIFT in
  let quotient:i32 = cast (quotient <: i64) <: i32 in
  let sub:i32 = quotient *! v_FIELD_MODULUS in
  value -! sub
