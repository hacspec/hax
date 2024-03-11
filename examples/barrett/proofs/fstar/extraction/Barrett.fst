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
          result >. (Core.Ops.Arith.Neg.neg v_FIELD_MODULUS <: i32) && result <. v_FIELD_MODULUS &&
          (result %! v_FIELD_MODULUS <: i32) =. (value %! v_FIELD_MODULUS <: i32)) =
  let t:i64 = (Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((9223372036854775807L -! (v_BARRETT_R >>! 1l <: i64) <: i64) >. t <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: 9223372036854775807 - (BARRETT_R >> 1) > t"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let t:i64 = t +! (v_BARRETT_R >>! 1l <: i64) in
  let quotient:i64 = t >>! v_BARRETT_SHIFT in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((quotient <=. 2147483647L <: bool) || (quotient >=. (-2147483648L) <: bool))
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: quotient <= 2147483647_i64 || quotient >= -2147483648_i64"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let quotient:i32 = cast (quotient <: i64) <: i32 in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.(((cast (quotient <: i32) <: i64) *! (cast (v_FIELD_MODULUS <: i32) <: i64) <: i64) <.
            9223372036854775807L
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: ((quotient as i64) * (FIELD_MODULUS as i64)) < 9223372036854775807"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let sub:i32 = quotient *! v_FIELD_MODULUS in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if
          ~.((9223372036854775807L -! (cast (value <: i32) <: i64) <: i64) >.
            ((cast (sub <: i32) <: i64) +! (-9223372036854775808L) <: i64)
            <:
            bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: 9223372036854775807 - (value as i64) > (sub as i64) + -9223372036854775808"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  value -! sub
