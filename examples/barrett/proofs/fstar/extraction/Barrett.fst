module Barrett
#set-options "--fuel 0 --ifuel 1 --z3rlimit 150"
open Core
open FStar.Mul

unfold
let t_FieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_R: i64 = 67108864L

let v_BARRETT_SHIFT: i64 = 26L

let v_FIELD_MODULUS: i32 = 3329l

let barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        (Core.Convert.f_from value <: i64) >=. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from value <: i64) <=. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg v_FIELD_MODULUS <: i32) && result <. v_FIELD_MODULUS &&
          (result %! v_FIELD_MODULUS <: i32) =. (value %! v_FIELD_MODULUS <: i32)) =
  let t:i64 = (Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER in
  let _:Prims.unit =
    Hax_lib.v_assert ((9223372036854775807L -! (v_BARRETT_R >>! 1l <: i64) <: i64) >. t <: bool)
  in
  let t:i64 = t +! (v_BARRETT_R >>! 1l <: i64) in
  let quotient:i64 = t >>! v_BARRETT_SHIFT in
  let _:Prims.unit =
    Hax_lib.v_assert ((quotient <=. 2147483647L <: bool) || (quotient >=. (-2147483648L) <: bool))
  in
  let quotient:i32 = cast (quotient <: i64) <: i32 in
  let _:Prims.unit =
    Hax_lib.v_assert (((cast (quotient <: i32) <: i64) *! (cast (v_FIELD_MODULUS <: i32) <: i64)
          <:
          i64) <.
        9223372036854775807L
        <:
        bool)
  in
  let sub:i32 = quotient *! v_FIELD_MODULUS in
  value -! sub
