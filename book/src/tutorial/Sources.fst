module Tutorial_src
#set-options "--fuel 0 --ifuel 1 --z3rlimit 150"
open Core
open FStar.Mul

// ANCHOR: F3
type t_F3 =
  | F3_E1 : t_F3
  | F3_E2 : t_F3
  | F3_E3 : t_F3

let t_F3_cast_to_repr (x: t_F3) : isize =
  match x with
  | F3_E1  -> isz 0
  | F3_E2  -> isz 1
  | F3_E3  -> isz 3
// ANCHOR_END: F3

// ANCHOR: barrett
unfold
let t_FieldElement = i32

let v_BARRETT_MULTIPLIER: i64 = 20159L

let v_BARRETT_R: i64 = 67108864L

let v_BARRETT_SHIFT: i64 = 26L

let v_FIELD_MODULUS: i32 = 3329l

let barrett_reduce (value: i32)
    : Pure i32
      (requires
        (Core.Convert.f_from value <: i64) >=. (Core.Ops.Arith.Neg.neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from value <: i64) <=. v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.Neg.neg v_FIELD_MODULUS <: i32) && result <. v_FIELD_MODULUS &&
          (result %! v_FIELD_MODULUS <: i32) =. (value %! v_FIELD_MODULUS <: i32)) =
  let t:i64 = (Core.Convert.f_from value <: i64) *! v_BARRETT_MULTIPLIER in
  let t:i64 = t +! (v_BARRETT_R >>! 1l <: i64) in
  let quotient:i64 = t >>! v_BARRETT_SHIFT in
  let quotient:i32 = cast (quotient <: i64) <: i32 in
  let sub:i32 = quotient *! v_FIELD_MODULUS in
  let _:Prims.unit = Tutorial_src.Math.Lemmas.cancel_mul_mod quotient 3329l in
  value -! sub
// ANCHOR_END: barrett

// ANCHOR: encrypt_decrypt
let decrypt (ciphertext key: u32) : u32 = ciphertext ^. key

let encrypt (plaintext key: u32) : u32 = plaintext ^. key
// ANCHOR_END: encrypt_decrypt







// ANCHOR: encrypt_decrypt_identity
let encrypt_decrypt_identity (key plaintext: u32)
    : Lemma (requires true)
      (ensures (decrypt (encrypt plaintext key <: u32) key <: u32) =. plaintext) = ()
// ANCHOR_END: encrypt_decrypt_identity

// ANCHOR: square
let square (x: u8) : u8 = x *! x
// ANCHOR_END: square

// ANCHOR: square_ensures
let square_ensures (x: u8)
    : Pure u8
      (requires x <. 16uy)
      (ensures fun result -> result >=. x) 
    = x *! x
// ANCHOR_END: square_ensures

// ANCHOR: square_option
let square_option (x: u8) : Core.Option.t_Option u8 =
  if x >=. 16uy
  then Core.Option.Option_None <: Core.Option.t_Option u8
  else Core.Option.Option_Some (x *! x) <: Core.Option.t_Option u8
// ANCHOR_END: square_option

// ANCHOR: square_requires
let square_requires (x: u8) 
  : Pure u8 (requires x <. 16uy) (requires fun _ -> True)
  = x *! x
// ANCHOR_END: square_requires

// ANCHOR: F
let v_Q: u16 = 2347us

type t_F = { f_v:f_v: u16{f_v <. v_Q} }
// ANCHOR_END: F

// ANCHOR: AddF
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Arith.t_Add t_F t_F =
  {
    f_Output = t_F;
    f_add_pre = (fun (self: t_F) (rhs: t_F) -> true);
    f_add_post = (fun (self: t_F) (rhs: t_F) (out: t_F) -> true);
    f_add = fun (self: t_F) (rhs: t_F) -> { 
          f_v = (self.f_v +! rhs.f_v <: u16) %! v_Q 
      } <: t_F
  }
// ANCHOR_END: AddF
