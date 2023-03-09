module Hacspec_poly1305
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

unfold
type polyKey_t = lseq uint8 32

let bLOCKSIZE: uint_size = 16

unfold
type polyBlock_t = lseq uint8 16

unfold
type poly1305Tag_t = lseq uint8 16

let subBlock = Hacspec_lib_tc.seq_t Secret_integers.u8_t

let blockIndex = uint_size

unfold
type fieldElement_t = nat_mod 0x03fffffffffffffffffffffffffffffffb
unfold
type fieldCanvas_t = lseq pub_uint8 131

let polyState = (fieldElement_t & fieldElement_t & polyKey_t)

unfold type sub_block_t = s: byte_seq {seq_len s < 16}
type block_index_t = x: uint_size {x < bLOCKSIZE}

let poly1305_encode_r (huhub: polyBlock_t) : fieldElement_t =
  let n:Secret_integers.u128_t =
    Hacspec_lib_tc.uint128_from_le_bytes (Hacspec_lib_tc.from_seq huhub)
  in
  let n = n &. Hacspec_lib_tc.secret (pub_u128 21267647620597763993911028882763415551) in
  from_secret_literal n

let poly1305_encode_block (xxb: polyBlock_t) : fieldElement_t =
  let n:Secret_integers.u128_t =
    Hacspec_lib_tc.uint128_from_le_bytes (Hacspec_lib_tc.from_seq xxb)
  in
  let f:fieldElement_t = from_secret_literal n in
  f +. pow2 128

let poly1305_encode_last (pad_len: block_index_t) (b: sub_block_t)
    : fieldElement_t =
  let n:Secret_integers.u128_t =
    Hacspec_lib_tc.uint128_from_le_bytes (Hacspec_lib_tc.from_slice b 0 (Hacspec_lib_tc.len b))
  in
  let f:fieldElement_t = from_secret_literal n in
  assert_norm (0x03fffffffffffffffffffffffffffffffb > pow2 129);
  Math.Lemmas.pow2_lt_compat 129 (8 * pad_len);
  f +. pow2 (8 * pad_len)

let poly1305_init (k: polyKey_t) : (fieldElement_t & fieldElement_t & polyKey_t) =
  let r:fieldElement_t = poly1305_encode_r (from_slice k 0 16) in
  Hacspec_lib_tc.zero, r, k

let poly1305_update_block (b: polyBlock_t) (st: (fieldElement_t & fieldElement_t & polyKey_t))
    : (fieldElement_t & fieldElement_t & polyKey_t) =
  let acc, r, k:(fieldElement_t & fieldElement_t & polyKey_t) = st in
  (poly1305_encode_block b +. acc) *. r, r, k

let poly1305_update_blocks
      (m: Hacspec_lib_tc.seq_t Secret_integers.u8_t)
      (st: (fieldElement_t & fieldElement_t & polyKey_t))
    : (fieldElement_t & fieldElement_t & polyKey_t) =
  let st:(fieldElement_t & fieldElement_t & polyKey_t) = st in
  let n_blocks:uint_size = Prims.op_Division (Hacspec_lib_tc.len m) bLOCKSIZE in
  Hacspec.Lib.foldi 0
    n_blocks
    (fun i st ->
        let block:polyBlock_t = from_seq (Hacspec_lib_tc.get_exact_chunk m bLOCKSIZE i) in
        poly1305_update_block block st)
    st

let poly1305_update_last
      (pad_len: block_index_t)
      (b: sub_block_t)
      (st: (fieldElement_t & fieldElement_t & polyKey_t))
    : (fieldElement_t & fieldElement_t & polyKey_t) =
  let st:(fieldElement_t & fieldElement_t & polyKey_t) = st in
  if Hacspec_lib_tc.len b <> 0
  then
    let acc, r, k:(fieldElement_t & fieldElement_t & polyKey_t) = st in
    (poly1305_encode_last pad_len b +. acc) *. r, r, k
  else st

let poly1305_update
      (m: Hacspec_lib_tc.seq_t Secret_integers.u8_t)
      (st: (fieldElement_t & fieldElement_t & polyKey_t))
    : (fieldElement_t & fieldElement_t & polyKey_t) =
  let st:(fieldElement_t & fieldElement_t & polyKey_t) = poly1305_update_blocks m st in
  let last:Hacspec_lib_tc.seq_t Secret_integers.u8_t =
    Hacspec_lib_tc.get_remainder_chunk m bLOCKSIZE
  in
  poly1305_update_last (Hacspec_lib_tc.len last) last st

let poly1305_finish (st: (fieldElement_t & fieldElement_t & polyKey_t)) : poly1305Tag_t =
  let acc, _, k:(fieldElement_t & fieldElement_t & polyKey_t) = st in
  let n:Secret_integers.u128_t =
    Hacspec_lib_tc.uint128_from_le_bytes (Hacspec_lib_tc.from_slice k 16 16)
  in
  let aby:Hacspec_lib_tc.seq_t Secret_integers.u8_t = nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) (17) acc in
  let a:Secret_integers.u128_t =
    Hacspec_lib_tc.uint128_from_le_bytes (Hacspec_lib_tc.from_slice aby 0 16)
  in
  from_seq (Hacspec_lib_tc.u128_to_le_bytes (a +. n))

let poly1305 (m: Hacspec_lib_tc.seq_t Secret_integers.u8_t) (key: polyKey_t) : poly1305Tag_t =
  let st:(fieldElement_t & fieldElement_t & polyKey_t) = poly1305_init key in
  let st:(fieldElement_t & fieldElement_t & polyKey_t) = poly1305_update m st in
  poly1305_finish st
