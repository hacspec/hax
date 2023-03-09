module Hacspec.Poly1305.Proof

open Hacspec.Lib
open FStar.Mul

module S = Spec.Poly1305
module H = Hacspec_poly1305
module Seq = Lib.Sequence

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let poly1305_encode_r_equiv (b:H.polyBlock_t)
  : Lemma (H.poly1305_encode_r b == S.poly1305_encode_r b)
          [SMTPat (H.poly1305_encode_r b)] =
  let n_1 = uint128_from_le_bytes (array_from_seq (16) (b)) in
  let lo : uint64 = Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b 0 8) in
  let hi : uint64 = Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b 8 8) in
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U64 #SEC (Lib.Sequence.sub b 0 8);
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U64 #SEC (Lib.Sequence.sub b 8 8);
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (array_from_seq 16 b);
  Lib.ByteSequence.nat_from_intseq_le_slice_lemma b 8;
  assert (v n_1 == v lo + pow2 64 * v hi);
  let mask128 = (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff)) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  assert (v mask128 == v mask0 + pow2 64 * v mask1);

  let n_2 = (n_1) &. mask128 in
  let lo' = lo &. mask0 in
  let hi' = hi &. mask1 in
  logand_spec n_1 mask128;
  logand_spec lo mask0;
  logand_spec hi mask1;
  assert (v n_2 == UInt.logand #128 (v n_1) (v mask128));
  assert (v lo' == UInt.logand #64 (v lo) (v mask0));
  assert (v hi' == UInt.logand #64 (v hi) (v mask1));
  logand_uint64_uint128 (v lo) (v mask0) (v hi) (v mask1)

let prime_equiv: squash (S.prime == 0x03fffffffffffffffffffffffffffffffb)
  = _ by (Tactics.compute ())

// [H.field_element_t] is [x:ℕ{x<S.prime}] while [S.felem] is
// [x:ℕ{x<=S.prime-1}]
let lemma_field_element_t_felem: squash (H.fieldElement_t == S.felem)
  = _ by FStar.Tactics.(
      compute ();
      // Rewrite [a≤b] into [a<b+1]
      l_to_r [binder_to_term (tcut (quote ((a:int) -> (b:int) -> squash ((a <= b) == (a < b + 1)))))];
      // normalize that `b+1`
      norm [primops];
      // we're left with the arrow goal [tcut] introduced, convert it to an implication
      trefl (); let _ = intros () in ()
    )

let poly1305_encode_block_equiv (b:H.polyBlock_t)
  : Lemma (H.poly1305_encode_block b == S.encode (seq_len b) b)
          [SMTPat (H.poly1305_encode_block b)] =
    Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (b <: Lib.ByteSequence.lbytes 16)

let poly1305_encode_last_equiv (b:H.sub_block_t {range (Seq.length b) U32})
  : Lemma (H.poly1305_encode_last (seq_len b) b == S.encode (seq_len b) b)
          [SMTPat (H.poly1305_encode_last (seq_len b) b)] =
  let fb = array_from_slice (secret (pub_u8 0x0)) (16) (b) (usize 0) (seq_len (b)) in
  let n_1 = uint128_from_le_bytes fb in
  let n_2 = Lib.ByteSequence.nat_from_bytes_le b in
  assert (Lib.Sequence.sub fb 0 (seq_len b) == b);
  assert (forall i. i >= seq_len b ==> v fb.[i] == 0);
  nat_from_zero_bytes (Lib.Sequence.sub fb (seq_len b) (seq_len fb - seq_len b));
  assert (Lib.ByteSequence.nat_from_intseq_le (Lib.Sequence.sub fb (seq_len b) (seq_len fb - seq_len b)) == 0);
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC fb;
  Lib.ByteSequence.nat_from_intseq_le_slice_lemma fb (seq_len b);
  assert (v n_1 == n_2)

let poly1305_init_equiv (k:H.polyKey_t)
  : Lemma ( let a , r, k'= H.poly1305_init k in
            let a', r'   = S.poly1305_init k in
            a == a' /\ r == r' /\ k' == k
          ) [SMTPat (H.poly1305_init k)] = ()

let poly1305_update_block_equiv (b:H.polyBlock_t) (st:H.polyState)
  : Lemma ( let a, r, k = st in
            let a' = S.poly1305_update1 r (seq_len b) b a in
            H.poly1305_update_block b st == (a', r, k)
          ) [SMTPat (H.poly1305_update_block b st)] = ()

let poly1305_update_last_equiv (b:H.sub_block_t{seq_len b < 16}) (st:H.polyState)
  : Lemma ( let a, r, k = st in
            let a' = S.poly1305_update_last r (seq_len b) b a in
            H.poly1305_update_last (seq_len b) b st == (a',r,k)
          ) [SMTPat (H.poly1305_update_last (seq_len b) b st)] = ()

let nat_to_byte_seq_le_lemma (n: pos) (len: uint_size) (x: nat_mod n) 
  : Lemma (forall (i: nat {i < len}). FStar.Seq.index (nat_to_byte_seq_le n len x) i
                            == uint #U8 #SEC ((x / pow2 (8 * i)) % pow2 8))
  = let y = x % (pow2 (8 * len)) in
    introduce forall (i: nat {i < len}). FStar.Seq.index (Lib.ByteSequence.nat_to_intseq_le #U8 #SEC len y) i
                               == uint #U8 #SEC ((x / pow2 (8 * i)) % pow2 8)
         with begin let j = len - i in
                    Lib.ByteSequence.index_nat_to_intseq_le #U8 #SEC len y i;
                    Math.Lemmas.modulo_division_lemma x (pow2 (8*i)) (pow2 (8*j));
                    Math.Lemmas.pow2_plus (8*(j-1)) 8;
                    Math.Lemmas.modulo_modulo_lemma (x / pow2 (8*i)) (pow2 8) (pow2 (8*(j-1)));
                    Math.Lemmas.pow2_plus (8*i) (8*j) end

let poly1305_finish_equiv (st:H.polyState)
  : Lemma (let (a,r,k) = st in
           H.poly1305_finish st == S.poly1305_finish k a)
           [SMTPat (H.poly1305_finish st)] =
  let (a,r,k) = st in
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (Lib.Sequence.sub k 16 16);
  let s : uint128 = Lib.ByteSequence.uint_from_bytes_le #U128 (Lib.Sequence.sub k 16 16) in
  let aby' = nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) 17 (a) in
  let aby = nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) 16 (a) in
  let sliced_aby = array_from_slice (secret (pub_u8 0x0)) 16 aby' 0 16 in
  nat_to_byte_seq_le_lemma 0x03fffffffffffffffffffffffffffffffb 17 a;
  nat_to_byte_seq_le_lemma 0x03fffffffffffffffffffffffffffffffb 16 a;
  assert (aby `Seq.equal` sliced_aby);
  Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC aby;
  let a' = a % pow2 128 in
  assert (aby == Lib.ByteSequence.nat_to_bytes_le #SEC 16 a');
  let afull = Lib.ByteSequence.nat_from_bytes_le aby in
  let a128 = Lib.ByteSequence.uint_from_bytes_le #U128 aby in
  Lib.ByteSequence.lemma_nat_to_from_bytes_le_preserves_value aby 16 (a % pow2 128);
  assert (afull == a % pow2 128);
  let res1 =  (a + v s) % pow2 128 in
  let res2 : uint128 = a128 +. s in
  Math.Lemmas.lemma_mod_add_distr (v s) a (pow2 128);
  assert ((a + v s) % pow2 128 == (a % pow2 128 + v s) % pow2 128);
  assert (res1 == v res2);
  let resby1 = Lib.ByteSequence.nat_to_bytes_le #SEC 16 res1 in
  let resby2 = Lib.ByteSequence.uint_to_bytes_le #U128 #SEC res2 in
  Lib.ByteSequence.lemma_uint_to_bytes_le_preserves_value res2;
  Lib.ByteSequence.lemma_nat_to_from_bytes_le_preserves_value resby1 16 res1;
  Lib.ByteSequence.nat_from_intseq_le_inj resby1 resby2;
  assert (resby1 == resby2);
  assert (H.poly1305_finish st == resby2);
  assert (S.poly1305_finish k a == resby1)

let foldi_relation
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (g: (i:uint_size{i < hi}) -> 'b -> 'b)
  (rel: (af:'a -> ag:'b -> Type0))
  (a0: 'a) (b0: 'b) (a0b0rel: squash (a0 `rel` b0))
  : Lemma (requires forall (i:uint_size{i < hi}) (a:'a) (b:'b)
                    . a `rel` b ==> f i a `rel` g i b)
          (ensures  foldi lo hi f a0 `rel` foldi lo hi g b0)
  = Hacspec.Lib.FoldiLemmas.foldi_relation lo hi f g rel a0 b0

let deconstructy_reconstruct_tup3 st: Lemma (
    let FStar.Pervasives.Native.Mktuple3 #_ #_ #_ a r k = st in
    Mktuple3?._1 st == a /\ r == Mktuple3?._2 st /\ k == Mktuple3?._3 st
  ) = ()

let poly1305_update (m_29 : byte_seq) (st_30 : H.polyState) : H.polyState =
   let st_31 : (H.fieldElement_t & H.fieldElement_t & H.polyKey_t) =
     H.poly1305_update_blocks (m_29) (st_30)
   in
   let last_32 : seq uint8 =
     seq_get_remainder_chunk (m_29) (H.bLOCKSIZE)
   in
   H.poly1305_update_last (seq_len (last_32)) (last_32) (st_31)

let poly1305_update_equiv (m:byte_seq) (st:H.polyState)
  : Lemma ( let a, r, k = st in
            let a' = S.poly1305_update m a r in
            H.poly1305_update m st == (a',r,k)
          ) [SMTPat (H.poly1305_update m st)]
  = Hacspec.Poly1305.Proof.Old.poly1305_update_equiv m st

let poly1305_mac_equiv (m:byte_seq) (k:H.polyKey_t)
  : Lemma (H.poly1305 m k == S.poly1305_mac m k) = ()
