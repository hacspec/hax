module OldExtraction.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type poly_key_t = lseq (uint8) (32)

let blocksize_v : uint_size =
  16

type poly_block_t = lseq (uint8) (16)

type poly1305_tag_t = lseq (uint8) (16)

type sub_block_t = s: byte_seq {seq_len s < 16}

type block_index_t = x: uint_size {x < blocksize_v}

type field_canvas_t = lseq (pub_uint8) (17)

type field_element_t = nat_mod 0x03fffffffffffffffffffffffffffffffb

type poly_state_t = (field_element_t & field_element_t & poly_key_t)

let poly1305_encode_r (b_0 : poly_block_t) : field_element_t =
  let n_1 : uint128 =
    uint128_from_le_bytes (array_from_seq (16) (b_0))
  in
  let n_1 =
    (n_1) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff))
  in
  nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_1)


let poly1305_encode_block (b_2 : poly_block_t) : field_element_t =
  let n_3 : uint128 =
    uint128_from_le_bytes (array_from_seq (16) (b_2))
  in
  let f_4 : field_element_t =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_3)
  in
  (f_4) +% (nat_pow2 (0x03fffffffffffffffffffffffffffffffb) (128))

let poly1305_encode_last
  (pad_len_5 : block_index_t)
  (b_6 : sub_block_t)
  : field_element_t =
  let n_7 : uint128 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x0)) (16) (b_6) (0) (seq_len (b_6)))
  in
  let f_8 : field_element_t =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_7)
  in
  assert_norm (0x03fffffffffffffffffffffffffffffffb > pow2 129);
  Math.Lemmas.pow2_lt_compat 129 (8 * pad_len_5);
  (f_8) +% (nat_pow2 (0x03fffffffffffffffffffffffffffffffb) ((8) * (pad_len_5)))

let poly1305_init (k_9 : poly_key_t) : poly_state_t =
  let r_10 : field_element_t =
    poly1305_encode_r (array_from_slice (secret (pub_u8 0x0)) (16) (k_9) (0) (16))
  in
  (nat_zero (0x03fffffffffffffffffffffffffffffffb), r_10, k_9)

let poly1305_update_block
  (b_11 : poly_block_t)
  (st_12 : poly_state_t)
  : poly_state_t =
  let (acc_13, r_14, k_15) : (field_element_t & field_element_t & poly_key_t) =
    st_12
  in
  (((poly1305_encode_block (b_11)) +% (acc_13)) *% (r_14), r_14, k_15)

let poly1305_update_blocks
  (m_16 : byte_seq)
  (st_17 : poly_state_t)
  : poly_state_t =
  let st_18 : (field_element_t & field_element_t & poly_key_t) =
    st_17
  in
  let n_blocks_19 : uint_size =
    (seq_len (m_16)) / (blocksize_v)
  in
  let (st_18) =
    foldi (0) (n_blocks_19) (fun i_20 (st_18) ->
      let block_21 : poly_block_t =
        array_from_seq (16) (seq_get_exact_chunk (m_16) (blocksize_v) (i_20))
      in
      let st_18 =
        poly1305_update_block (block_21) (st_18)
      in
      (st_18))
    (st_18)
  in
  st_18

let poly1305_update_last
  (pad_len_22 : block_index_t)
  (b_23 : sub_block_t)
  (st_24 : poly_state_t)
  : poly_state_t =
  let st_25 : (field_element_t & field_element_t & poly_key_t) =
    st_24
  in
  let (st_25) =
    if (seq_len (b_23)) <> (0) then begin
      let (acc_26, r_27, k_28) : (field_element_t & field_element_t & poly_key_t
        ) =
        st_25
      in
      let st_25 =
        (
          ((poly1305_encode_last (pad_len_22) (b_23)) +% (acc_26)) *% (r_27),
          r_27,
          k_28
        )
      in
      (st_25)
    end else begin (st_25)
    end
  in
  st_25

let poly1305_update (m_29 : byte_seq) (st_30 : poly_state_t) : poly_state_t =
  let st_31 : (field_element_t & field_element_t & poly_key_t) =
    poly1305_update_blocks (m_29) (st_30)
  in
  let last_32 : seq uint8 =
    seq_get_remainder_chunk (m_29) (blocksize_v)
  in
  poly1305_update_last (seq_len (last_32)) (last_32) (st_31)

// let poly1305_encode_r_eq x = assert (poly1305_encode_r x == Hacspec_poly1305.poly1305_encode_r x)
// let poly1305_encode_block_eq x = assert (poly1305_encode_block x == Hacspec_poly1305.poly1305_encode_block x)
// let poly1305_encode_last_eq x y = assert (poly1305_encode_last x y == Hacspec_poly1305.poly1305_encode_last x y)
// let poly1305_init_eq x = assert (poly1305_init x == Hacspec_poly1305.poly1305_init x)
// let poly1305_update_block_eq x y = assert (poly1305_update_block x y == Hacspec_poly1305.poly1305_update_block x y)
// let poly1305_update_blocks_eq x y = assert (poly1305_update_blocks x y == Hacspec_poly1305.poly1305_update_blocks x y)
//   by (Tactics.compute (); Tactics.trefl ())
// let poly1305_update_last_eq x y z = assert (poly1305_update_last x y z == Hacspec_poly1305.poly1305_update_last x y z)

let poly1305_update_eq m st:
  Lemma (poly1305_update m st == Hacspec_poly1305.poly1305_update m st) 
    [SMTPat (poly1305_update m st)]
  = let x = seq_get_remainder_chunk m blocksize_v in
    assert (poly1305_update m st == 
           Hacspec_poly1305.(poly1305_update_last (seq_len x) x (poly1305_update_blocks m st)))
    by (Tactics.compute (); Tactics.trefl ())

let poly1305_finish (st_33 : poly_state_t) : poly1305_tag_t =
  let (acc_34, _, k_35) : (field_element_t & field_element_t & poly_key_t) =
    st_33
  in
  let n_36 : uint128 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x0)) (16) (k_35) (16) (16))
  in
  let aby_37 : seq uint8 =
    nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) (17) (acc_34)
  in
  let a_38 : uint128 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x0)) (16) (aby_37) (0) (16))
  in
  array_from_seq (16) (uint128_to_le_bytes ((a_38) +. (n_36)))


let poly1305 (m_39 : byte_seq) (key_40 : poly_key_t) : poly1305_tag_t =
  let st_41 : (field_element_t & field_element_t & poly_key_t) =
    poly1305_init (key_40)
  in
  let st_41 =
    poly1305_update (m_39) (st_41)
  in
  poly1305_finish (st_41)

let poly1305_eq m k: Lemma (poly1305 m k == Hacspec_poly1305.poly1305 m k) =
  ()
