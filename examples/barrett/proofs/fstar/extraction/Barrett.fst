module Barrett
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_FieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_R: i64 = 67108864L

let v_BARRETT_SHIFT: i64 = 26L

let v_FIELD_MODULUS: i32 = 3329l

class t_IsRefinement (v_Self: Type) = {
  f_InnerType:Type;
  f_refine_pre:f_InnerType -> bool;
  f_refine_post:f_InnerType -> v_Self -> bool;
  f_refine:x0: f_InnerType
    -> Prims.Pure v_Self (f_refine_pre x0) (fun result -> f_refine_post x0 result);
  f_value_pre:v_Self -> bool;
  f_value_post:v_Self -> f_InnerType -> bool;
  f_value:x0: v_Self
    -> Prims.Pure f_InnerType (f_value_pre x0) (fun result -> f_value_post x0 result)
}

type t_Bounded (v_MIN: i128) (v_MAX: i128) = | Bounded : i32 -> t_Bounded v_MIN v_MAX

let impl__get_value (v_MIN v_MAX: i128) (self: t_Bounded v_MIN v_MAX) : i32 = self._0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (v_MIN v_MAX: i128) : Core.Convert.t_From (t_Bounded v_MIN v_MAX) i32 =
  {
    f_from_pre
    =
    (fun (x: i32) -> (cast (x <: i32) <: i128) >=. v_MIN && (cast (x <: i32) <: i128) <=. v_MAX);
    f_from_post = (fun (x: i32) (out: t_Bounded v_MIN v_MAX) -> true);
    f_from
    =
    fun (x: i32) ->
      let _:Prims.unit = () <: Prims.unit in
      Bounded x <: t_Bounded v_MIN v_MAX
  }

let barrett_reduce (value: t_Bounded (pub_i128 (-67108864)) (pub_i128 67108864))
    : t_Bounded (pub_i128 (-3328)) (pub_i128 3328) =
  let t:i64 =
    (Core.Convert.f_from (impl__get_value (pub_i128 (-67108864)) (pub_i128 67108864) value <: i32)
      <:
      i64) *!
    v_BARRETT_MULTIPLIER
  in
  let t:i64 = t +! (v_BARRETT_R >>! 1l <: i64) in
  let quotient:i64 = t >>! v_BARRETT_SHIFT in
  let quotient:i32 = cast (quotient <: i64) <: i32 in
  let sub:i32 = quotient *! v_FIELD_MODULUS in
  let _:Prims.unit = Math.Lemmas.cancel_mul_mod (v quotient) 3329 in
  Core.Convert.f_from ((impl__get_value (pub_i128 (-67108864)) (pub_i128 67108864) value <: i32) -!
      sub
      <:
      i32)
