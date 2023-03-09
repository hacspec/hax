module Hacspec.Chacha20.Proof

open FStar.Tactics
open Hacspec.Lib
open FStar.Mul
open Hacspec_chacha20

module S = Spec.Chacha20
module H = Hacspec_chacha20
module LSeq = Lib.Sequence
module Seq = FStar.Seq
module LSeqLemmas = Lib.Sequence.Lemmas

module LC = Lib.LoopCombinators

let rec make_list (elem: 'a) (n: nat): list 'a
  = if n = 0 then [] else elem::make_list elem (n-1)

let unfold_repeat (f: 'a -> 'a) (acc0: 'a) (i:pos)
  : Lemma (LC.repeat i f acc0 == f (LC.repeat (i - 1) f acc0))
  = LC.unfold_repeat i f acc0 (i-1) 

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let equiv_line (a b d: state_idx_t) (s: pos {s < 32}) (state: state_t)
  : Lemma (S.line a b d (pub_u32 s) state == H.chacha20_line a b d s state)
          [SMTPat (H.chacha20_line a b d s state)]
  = assert (S.line a b d (pub_u32 s) state `LSeq.equal` H.chacha20_line a b d s state)

let equiv_constants_init
  : squash (LSeq.map secret S.chacha20_constants == chacha20_constants_init)
  = let l = S.([c0;c1;c2;c3]) in
    assert_norm (FStar.List.Tot.length l == 4);
    assert_norm S.(let h (i:nat{i<4}) = FStar.List.Tot.index l i in h 0 = c0 /\ h 1 = c1 /\ h 2 = c2 /\ h 3 = c3);
    LSeq.eq_intro (LSeq.map #_ #_ #(4 <: size_nat) secret S.chacha20_constants) (chacha20_constants_init)

let equiv_init (key: chaChaKey_t) (iv: chaChaIV_t) (ctr: uint32)
  : Lemma (S.chacha20_init key iv (v ctr) == H.chacha20_init key iv ctr)
          [SMTPat (H.chacha20_init key iv ctr)]
  = ()

let equiv_quarter_round (a b c d: state_idx_t) (state: state_t)
  : Lemma (S.quarter_round a b c d state == H.chacha20_quarter_round a b c d state)
          [SMTPat (H.chacha20_quarter_round a b c d state)]
  = ()

let equiv_double_round (state: state_t)
  : Lemma (S.double_round state == H.chacha20_double_round state)
          [SMTPat (H.chacha20_double_round state)]
  = ()

#push-options "--max_fuel 0 --z3rlimit 15"
let equiv_rounds (st: state_t)
  : Lemma (S.rounds st == H.chacha20_rounds st)
          [SMTPat (H.chacha20_rounds st)]
  = assert (S.rounds st == chacha20_rounds st) 
        by (norm [delta_only [`%S.rounds; `%chacha20_rounds]];
            iter (fun _ -> l_to_r [`unfold_repeat]) (make_list () 10);
            l_to_r [`LC.eq_repeat0];
            norm [primops; iota; delta_only [`%usize; `%foldi]; zeta_full])
#pop-options

let equiv_core (ctr: uint32) (st0: state_t)
  : Lemma (S.chacha20_core (v ctr) st0 == chacha20_core ctr st0)
          [SMTPat (H.chacha20_core ctr st0)]
  = let s0 = st0 in
    let s1 = array_upd st0 (usize 12) (
                      (array_index (s0) (usize 12)) +. (ctr)) in
    let k = H.chacha20_rounds s1 in
    let ka = k `array_add (+.)` s1 in
    let kb = k `array_add (+.)` s0 in
    let kb' = array_upd kb (usize 12) (
                      (array_index (kb) (usize 12)) +. (ctr)) in
    assert (u32 (v ctr) == ctr);
    assert(S.chacha20_add_counter s0 (v ctr) == s1);
    assert(S.rounds s1 == H.chacha20_rounds s1);
    assert(S.sum_state k s0 == kb);
    assert(S.chacha20_add_counter kb (v ctr) == kb');
    assert(ka == H.chacha20_core ctr st0);
    assert(kb' == S.chacha20_core (v ctr) st0);
    assert(forall i. i <> 12 ==> s0.[i] ==  s1.[i]);
    assert(forall i. i <> 12 ==> ka.[i] ==  kb.[i]);
    assert(forall i. i <> 12 ==> ka.[i] ==  kb'.[i]);
    assert(s1.[12] ==  s0.[12] +. ctr);
    assert(ka.[12] ==  k.[12] +. s1.[12]);
    assert(kb.[12] ==  k.[12] +. s0.[12]);
    assert(kb'.[12] ==  k.[12] +. s0.[12] +. ctr);
    assert(kb'.[12] ==  k.[12] +. (s0.[12] +. ctr));
    assert(kb'.[12] ==  k.[12] +. s1.[12]);
    assert(forall i. i >= 0 /\ i < 16 ==> ka.[i] ==  kb'.[i]);
    LSeq.eq_intro ka kb'

let equiv_key_block (state: state_t)
  : Lemma (S.chacha20_key_block state == chacha20_key_block state)
          [SMTPat (H.chacha20_key_block state)]
  = ()

let equiv_key_block0 (key: chaChaKey_t) (iv: chaChaIV_t)
  : Lemma (chacha20_key_block0 key iv == S.chacha20_key_block0 key iv)
          [SMTPat (H.chacha20_key_block0 key iv)]
  = ()

let equiv_encrypt_block (st0: state_t) (ctr: uint32) (plain: block_t)
  : Lemma (H.chacha20_encrypt_block st0 ctr plain == S.chacha20_encrypt_block st0 (v ctr) plain)
          [SMTPat (H.chacha20_encrypt_block st0 ctr plain)]
  = ()

let equiv_encrypt_last (st0:state_t) (ctr:uint32) (plain: byte_seq {seq_len plain < 64})
  : Lemma (H.chacha20_encrypt_last st0 ctr plain == S.chacha20_encrypt_last st0 (v ctr) (seq_len plain) plain)
          [SMTPat (H.chacha20_encrypt_last st0 ctr plain)]
  = ()

open Hacspec.Lib.FoldiLemmas


let chacha20_update_ (st0 : state_t) (m : byte_seq) : Hacspec_lib_tc.seq_t Secret_integers.u8_t =
  let blocks_out = Hacspec_lib_tc.new_seq (Hacspec_lib_tc.len m) in
  let n_blocks : uint_size = Hacspec_lib_tc.num_exact_chunks m 64 in
  let blocks_out =
    foldi 0 n_blocks (fun i blocks_out ->
      let msg_block : seq uint8 =
        Hacspec_lib_tc.get_exact_chunk m 64 i
      in
      let b : block_t =
        chacha20_encrypt_block st0 (Hacspec.Lib.secret (pub_u32 i)) (
          array_from_seq (64) (msg_block))
      in
      let blocks_out =
        Hacspec_lib_tc.set_exact_chunk (blocks_out) 64 i b
      in
      blocks_out)
    blocks_out
  in
  let last_block: seq uint8 = seq_get_remainder_chunk m 64 in
    if seq_len last_block <> 0 then
      let b : seq uint8 =
        chacha20_encrypt_last st0 (Hacspec.Lib.secret (pub_u32 n_blocks)) last_block
      in
      seq_set_chunk blocks_out 64 n_blocks b
    else blocks_out

let chacha20_update_equiv_ (st0 : state_t) (cipher : byte_seq) 
  : Lemma (chacha20_update_ st0 cipher == S.chacha20_update st0 cipher)
  = let blocks_out: seq uint8 = seq_new_ (secret (pub_u8 0x0)) (seq_len cipher) in
    let n_blocks: uint_size = seq_num_exact_chunks cipher 64 in
  
  let f (i: nat {i<n_blocks}) (msg_block: lseq uint8 64): block_t = 
    chacha20_encrypt_block st0 (secret (pub_u32 i)) (array_from_seq 64 msg_block)
  in
  let blocks_out' = map_blocks_foldi #uint8 #(seq_len cipher) 64 n_blocks n_blocks cipher blocks_out f in
  LSeqLemmas.map_blocks_extensionality 64 cipher (S.chacha20_encrypt_block st0) (S.chacha20_encrypt_last st0) f (S.chacha20_encrypt_last st0);
  LSeq.lemma_map_blocks 64 cipher f (S.chacha20_encrypt_last st0);
  map_blocks_foldi_equiv_lemma #uint8 (seq_len cipher) 64 n_blocks n_blocks cipher blocks_out f;
  LSeq.lemma_map_blocks_multi 64 n_blocks n_blocks (Seq.slice cipher 0 (n_blocks * 64)) f;
  let last_block: seq uint8 = seq_get_remainder_chunk cipher 64 in
  assert (S.chacha20_update st0 cipher `LSeq.equal`
         (if seq_len last_block = 0 then blocks_out'
          else seq_set_chunk blocks_out' 64 n_blocks (chacha20_encrypt_last st0 (secret (pub_u32 n_blocks)) last_block)))


let chacha20_update_equiv (st0 : state_t) (cipher : byte_seq) 
  : Lemma (H.chacha20_update st0 cipher == S.chacha20_update st0 cipher)
          [SMTPat (H.chacha20_update st0 cipher)]
  = assert (H.chacha20_update st0 cipher == chacha20_update_ st0 cipher) by (
           Tactics.compute ();
           Tactics.trefl ()
    );
    chacha20_update_equiv_ st0 cipher

let chacha20_equiv (key: chaChaKey_t) (iv: chaChaIV_t) (ctr: pub_uint32) (m: byte_seq)
  : Lemma (S.chacha20_encrypt_bytes key iv (v ctr) m == H.chacha20 key iv ctr m)
          [SMTPat (H.chacha20 key iv ctr m)]
  = ()

