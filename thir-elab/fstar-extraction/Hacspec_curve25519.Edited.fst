module Hacspec_curve25519
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

unfold
type x25519FieldElement_t =
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
unfold
type fieldCanvas_t = lseq pub_uint8 256

unfold
type scalar_t = nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000
unfold
type scalarCanvas_t = lseq pub_uint8 256

let point = (x25519FieldElement_t & x25519FieldElement_t)

unfold
type x25519SerializedPoint_t = lseq uint8 32

unfold
type x25519SerializedScalar_t = lseq uint8 32

let mask_scalar (s: x25519SerializedScalar_t) : x25519SerializedScalar_t =
  let k:x25519SerializedScalar_t = s in
  let k:x25519SerializedScalar_t = k.[ 0l ] <- k.[ 0l ] &. Hacspec_lib_tc.secret 248uy in
  let k:x25519SerializedScalar_t = k.[ 31l ] <- k.[ 31l ] &. Hacspec_lib_tc.secret 127uy in
  k.[ 31l ] <- k.[ 31l ] |. Hacspec_lib_tc.secret 64uy

let decode_scalar (s: x25519SerializedScalar_t) : scalar_t =
  let k:x25519SerializedScalar_t = mask_scalar s in
  from_byte_seq_le k

let decode_point (u: x25519SerializedPoint_t) : (x25519FieldElement_t & x25519FieldElement_t) =
  let u_:x25519SerializedPoint_t = u in
  let u_:x25519SerializedPoint_t = u_.[ 31l ] <- u_.[ 31l ] &. Hacspec_lib_tc.secret 127uy in
  from_byte_seq_le u_, from_literal (pub_u128 1)

let encode_point (p: (x25519FieldElement_t & x25519FieldElement_t)) : x25519SerializedPoint_t =
  let x, y:(x25519FieldElement_t & x25519FieldElement_t) = p in
  let b:x25519FieldElement_t = x *. inv y in
  Hacspec_lib_tc.update_start new_ (to_byte_seq_le b)

let point_add_and_double
      (q: (x25519FieldElement_t & x25519FieldElement_t))
      (np:
          ((x25519FieldElement_t & x25519FieldElement_t) &
            (x25519FieldElement_t & x25519FieldElement_t)))
    : ((x25519FieldElement_t & x25519FieldElement_t) & (x25519FieldElement_t & x25519FieldElement_t)
    ) =
  let nq, nqp1:((x25519FieldElement_t & x25519FieldElement_t) &
    (x25519FieldElement_t & x25519FieldElement_t)) =
    np
  in
  let x_1, _z_1:(x25519FieldElement_t & x25519FieldElement_t) = q in
  let x_2, z_2:(x25519FieldElement_t & x25519FieldElement_t) = nq in
  let x_3, z_3:(x25519FieldElement_t & x25519FieldElement_t) = nqp1 in
  let a:x25519FieldElement_t = x_2 +. z_2 in
  let aa:x25519FieldElement_t = pow a (pub_u128 2) in
  let b:x25519FieldElement_t = x_2 -. z_2 in
  let bb:x25519FieldElement_t = b *. b in
  let e:x25519FieldElement_t = aa -. bb in
  let c:x25519FieldElement_t = x_3 +. z_3 in
  let d:x25519FieldElement_t = x_3 -. z_3 in
  let da:x25519FieldElement_t = d *. a in
  let cb:x25519FieldElement_t = c *. b in
  let x_3:x25519FieldElement_t = pow (da +. cb) (pub_u128 2) in
  let z_3:x25519FieldElement_t = x_1 *. pow (da -. cb) (pub_u128 2) in
  let x_2:x25519FieldElement_t = aa *. bb in
  let e121665:x25519FieldElement_t = from_literal (pub_u128 121665) in
  let z_2:x25519FieldElement_t = e *. (aa +. e121665 *. e) in
  FStar.Pervasives.Native.Mktuple2 x_2 z_2, FStar.Pervasives.Native.Mktuple2 x_3 z_3

let swap
      (x:
          ((x25519FieldElement_t & x25519FieldElement_t) &
            (x25519FieldElement_t & x25519FieldElement_t)))
    : ((x25519FieldElement_t & x25519FieldElement_t) & (x25519FieldElement_t & x25519FieldElement_t)
    ) =
  let x0, x1:((x25519FieldElement_t & x25519FieldElement_t) &
    (x25519FieldElement_t & x25519FieldElement_t)) =
    x
  in
  x1, x0

let montgomery_ladder (k: scalar_t) (init: (x25519FieldElement_t & x25519FieldElement_t))
    : (x25519FieldElement_t & x25519FieldElement_t) =
  let inf:(x25519FieldElement_t & x25519FieldElement_t) =
    from_literal (pub_u128 1), from_literal (pub_u128 0)
  in
  let
  (acc:
    ((x25519FieldElement_t & x25519FieldElement_t) & (x25519FieldElement_t & x25519FieldElement_t))):(
    (x25519FieldElement_t & x25519FieldElement_t) & (x25519FieldElement_t & x25519FieldElement_t)) =
    inf, init
  in
  let acc:((x25519FieldElement_t & x25519FieldElement_t) &
    (x25519FieldElement_t & x25519FieldElement_t)) =
    Dummy.foldi 0
      256
      (fun i acc ->
          if bit k (255 - i)
          then
            let acc:((x25519FieldElement_t & x25519FieldElement_t) &
              (x25519FieldElement_t & x25519FieldElement_t)) =
              swap acc
            in
            let acc:((x25519FieldElement_t & x25519FieldElement_t) &
              (x25519FieldElement_t & x25519FieldElement_t)) =
              point_add_and_double init acc
            in
            swap acc
          else point_add_and_double init acc)
      acc
  in
  let out, _:((x25519FieldElement_t & x25519FieldElement_t) &
    (x25519FieldElement_t & x25519FieldElement_t)) =
    acc
  in
  out

let x25519_scalarmult (s: x25519SerializedScalar_t) (p: x25519SerializedPoint_t)
    : x25519SerializedPoint_t =
  let s_:scalar_t = decode_scalar s in
  let p_:(x25519FieldElement_t & x25519FieldElement_t) = decode_point p in
  let r:(x25519FieldElement_t & x25519FieldElement_t) = montgomery_ladder s_ p_ in
  encode_point r

let x25519_secret_to_public (s: x25519SerializedScalar_t) : x25519SerializedPoint_t =
  let base:x25519SerializedPoint_t = new_ in
  let base:x25519SerializedPoint_t = base.[ 0l ] <- Hacspec_lib_tc.secret 9uy in
  x25519_scalarmult s base