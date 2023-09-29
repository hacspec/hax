module Libcrux.Kem.Kyber768.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_KyberFieldElement = i32

let v_BARRETT_SHIFT: i32 = 26l

let v_BARRETT_R: i32 = 1l >>. v_BARRETT_SHIFT

let v_BARRETT_MULTIPLIER: i32 = 20159l

let barrett_reduce (value: i32) : i32 =
  let quotient:i32 =
    ((value *. v_BARRETT_MULTIPLIER <: i32) +. (v_BARRETT_R <<. 1l <: i32) <: i32) <<.
    v_BARRETT_SHIFT
  in
  value -. (quotient *. Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS <: i32)

let v_MONTGOMERY_SHIFT: i64 = 16L

let v_MONTGOMERY_R: i64 = 1L >>. v_MONTGOMERY_SHIFT

let v_INVERSE_OF_MODULUS_MOD_R: i64 = 3327L

let montgomery_reduce (value: i32) : i32 =
  let (t: i64):i64 = (Core.Convert.f_from value <: i64) *. v_INVERSE_OF_MODULUS_MOD_R in
  let (t: i32):i32 = cast (t &. (v_MONTGOMERY_R -. 1L <: i64)) in
  (value -. (t *. Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS <: i32) <: i32) <<.
  v_MONTGOMERY_SHIFT

let to_montgomery_domain (value: i32) : i32 = montgomery_reduce (1353l *. value <: i32)

type t_KyberPolynomialRingElement = { f_coefficients:array i32 256sz }

let v_ZERO_under_impl: t_KyberPolynomialRingElement =
  {
    f_coefficients = Rust_primitives.Hax.repeat 0l 256sz
  }

(*
let impl: Core.Ops.Index.t_Index t_KyberPolynomialRingElement usize =
  {
    output = i32;
    index
    =
    fun (self: t_KyberPolynomialRingElement) (index: usize) ->
      self.Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients.[ index ]
  }

let impl: Core.Iter.Traits.Collect.t_IntoIterator t_KyberPolynomialRingElement =
  {
    item = i32;
    intoIter = Core.Array.Iter.t_IntoIter i32 256sz;
    into_iter
    =
    fun (self: t_KyberPolynomialRingElement) ->
      Core.Iter.Traits.Collect.IntoIterator.into_iter self
          .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
  }

let impl: Core.Ops.Arith.t_Add t_KyberPolynomialRingElement t_KyberPolynomialRingElement =
  {
    output = t_KyberPolynomialRingElement;
    add
    =
    fun (self: t_KyberPolynomialRingElement) (other: t_KyberPolynomialRingElement) ->
      let result:t_KyberPolynomialRingElement = v_ZERO_under_impl in
      let result:t_KyberPolynomialRingElement =
        Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT
                })
            <:
            _)
          result
          (fun result i ->
              {
                result with
                Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                =
                Rust_primitives.Hax.update_at result
                    .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  i
                  ((self.Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients.[
                        i ]
                      <:
                      i32) +.
                    (other.Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients.[
                        i ]
                      <:
                      i32)
                    <:
                    i32)
                <:
                t_KyberPolynomialRingElement
              })
      in
      result
  }

let impl: Core.Ops.Arith.t_Sub t_KyberPolynomialRingElement t_KyberPolynomialRingElement =
  {
    output = t_KyberPolynomialRingElement;
    sub
    =
    fun (self: t_KyberPolynomialRingElement) (other: t_KyberPolynomialRingElement) ->
      let result:t_KyberPolynomialRingElement = v_ZERO_under_impl in
      let result:t_KyberPolynomialRingElement =
        Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT
                })
            <:
            _)
          result
          (fun result i ->
              {
                result with
                Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                =
                Rust_primitives.Hax.update_at result
                    .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  i
                  ((self.Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients.[
                        i ]
                      <:
                      i32) -.
                    (other.Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients.[
                        i ]
                      <:
                      i32)
                    <:
                    i32)
                <:
                t_KyberPolynomialRingElement
              })
      in
      result
  }
*)
