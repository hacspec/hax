module Hacspec.Lib.FoldiLemmas

open FStar.Tactics
open Hacspec.Lib
open FStar.Mul
open Hacspec.Chacha20

module S = Spec.Chacha20
module H = Hacspec.Chacha20
module LSeq = Lib.Sequence
module Seq = FStar.Seq
module LSeqLemmas = Lib.Sequence.Lemmas

module LC = Lib.LoopCombinators

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let rec foldi_relation
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (g: (i:uint_size{i < hi}) -> 'b -> 'b)
  (rel: (af:'a -> ag:'b -> Type0))
  (a0: 'a) (b0: 'b {a0 `rel` b0})
  : Lemma (requires forall (i:uint_size{i < hi}) (a:'a) (b:'b)
                    . a `rel` b ==> f i a `rel` g i b)
          (ensures  foldi lo hi f a0 `rel` foldi lo hi g b0)
  = if lo = hi
    then ( unfold_foldi hi hi f a0;
           unfold_foldi hi hi g b0 )
    else ( unfold_foldi_right lo hi f a0;
           unfold_foldi_right lo hi g b0;
           foldi_relation lo (hi-1) f g rel a0 b0 )

let foldi_extensionality
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (g: (i:uint_size{i < hi}) -> 'a -> 'a)
  (init: 'a)
  : Lemma (requires forall i a. f i a == g i a)
          (ensures  foldi lo hi f init == foldi lo hi g init)
  = foldi_relation lo hi f g (==) init init

unfold let map_blocks_foldi_fun
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (original_s: lseq 'a len)
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  (i: uint_size{i<max}) (s: lseq 'a len)
  = seq_set_exact_chunk #'a #len s blocksize i (f i (seq_get_exact_chunk #'a original_s blocksize i))

unfold let map_blocks_foldi
    (#len: uint_size) (blocksize: size_pos)
    (max: uint_size {max * blocksize <= len})
    (n: uint_size {n * blocksize <= len /\ n <= max})
    (original_s: lseq 'a len)
    (s: lseq 'a len)
    (f:(i:uint_size{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
    : lseq 'a len
  = foldi #(lseq 'a len) 0 n (map_blocks_foldi_fun len blocksize max original_s f) s

let map_blocks_foldi_fun_preserves_lemma
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (original_s: lseq 'a len)
  (f:(i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  (i: uint_size{i < max}) (s: lseq 'a len)
  : Lemma ( forall (j:nat{j >= blocksize * (i+1) /\ j < len}).
            LSeq.index s j == LSeq.index (map_blocks_foldi_fun len blocksize max original_s f i s) j)
  = let r = seq_set_exact_chunk #_ #len s blocksize i (f i (seq_get_exact_chunk s blocksize i)) in
    let out_len = seq_chunk_len s blocksize i in
    assert (out_len == ( if blocksize * (i+1) > len
                         then ( if blocksize * i < len
                                then framed_mod_lemma i len blocksize;
                                len % blocksize )
                         else blocksize));
    let r' = LSeq.update_sub s (blocksize * i) out_len (f i (seq_get_exact_chunk original_s blocksize i)) in
    assert ((forall (k:nat{(k < blocksize * i \/ blocksize * i +out_len <= k) /\ k<len}). LSeq.index r' k == LSeq.index s k));
    if blocksize * (i + 1) <= Seq.length s 
    then assert (forall (j:nat{j >= blocksize*(i+1) /\ j<len}). LSeq.index r' j == LSeq.index s j)

let rec map_blocks_foldi_preserves_lemma
    (len: uint_size) (blocksize: size_pos)
    (max: uint_size {max * blocksize <= len})
    (n: uint_size {n * blocksize <= len /\ n <= max})
    (original_s: lseq 'a len)
    (s0: lseq 'a len)
    (f:(i:uint_size{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  : Lemma (forall (i:nat{i >= blocksize * n /\ i < len}). Seq.index s0 i == Seq.index (map_blocks_foldi blocksize max n original_s s0 f) i)
   = if n = 0 then unfold_foldi 0 0 (map_blocks_foldi_fun len blocksize max original_s f) s0 
     else begin unfold_foldi_right 0 n (map_blocks_foldi_fun len blocksize max original_s f) s0;
                map_blocks_foldi_preserves_lemma len blocksize max (n - 1) original_s s0 f;
                introduce forall (i: nat{i < max}) (s: lseq 'a len). forall (j:nat{j >= blocksize * (i+1) /\ j < len}).
                                Seq.index s j == Seq.index (map_blocks_foldi_fun len blocksize max original_s f i s) j
                     with map_blocks_foldi_fun_preserves_lemma len blocksize max original_s f i s end

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
let map_blocks_f_equiv_lemma
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (original_s: lseq 'a len)
  (f: (i:nat{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  (i: nat{i < max})
  (updated_s: lseq 'a len)
  (acc: lseq 'a (i * blocksize) {forall (j:nat{j < i * blocksize}). Seq.index acc j == Seq.index updated_s j})
  : Lemma ( let slice_s = Seq.slice original_s 0 (max * blocksize) in
            forall (j: nat{j < (i+1) * blocksize}).
                  Seq.index (LSeq.map_blocks_f blocksize max slice_s f i acc) j
               == Seq.index (seq_set_exact_chunk #_ #len updated_s blocksize i (f i (seq_get_exact_chunk original_s blocksize i))) j )
  = Math.Lemmas.lemma_mult_le_right blocksize (i+1) max;
    let idx_start, out_len = blocksize * i, seq_chunk_len updated_s blocksize i in
    let r1 = Seq.append acc (f i (Seq.slice original_s (i*blocksize) ((i+1)*blocksize))) in
    let block2 = f i (seq_get_exact_chunk original_s blocksize i) in
    let r2 = LSeq.update_sub updated_s idx_start out_len block2 in
    introduce forall (j:nat{j < (i+1) * blocksize}). Seq.index r1 j == Seq.index r2 j
    with if j < i * blocksize
         then eliminate forall (k:nat{(0 <= k /\ k < idx_start) \/ (idx_start + out_len <= k /\ k < len)}). LSeq.index r2 k == LSeq.index updated_s k
              with j

let rec map_blocks_foldi_equiv_lemma
  (len: uint_size) (blocksize: size_pos)
  (max: uint_size {max * blocksize <= len})
  (n: uint_size {n * blocksize <= len /\ n <= max})
  (original_s: lseq 'a len)
  (s: lseq 'a len)
  (f:(i:uint_size{i < max}) -> lseq 'a blocksize -> lseq 'a blocksize)
  : Lemma (ensures (
    let slice_s = Seq.slice original_s 0 (max * blocksize) in
    let r1 = LC.repeat_gen n (LSeq.map_blocks_a 'a blocksize max) (LSeq.map_blocks_f blocksize max slice_s f) Seq.empty in
    let r2 = map_blocks_foldi blocksize max n original_s s f in
    (forall (i:nat{i < blocksize * n}). Seq.index r1 i == Seq.index r2 i)
  )) (decreases n)
  = if n <> 0 then
      let n': uint_size = n - 1 in
      let slice_s = Seq.slice original_s 0 (max * blocksize) in
      let r1' = LC.repeat_gen (n-1) (LSeq.map_blocks_a 'a blocksize max) (LSeq.map_blocks_f blocksize max slice_s f) Seq.empty in
      let r2' = map_blocks_foldi blocksize max (n - 1) original_s s f in
      let all1 = LSeq.map_blocks_f blocksize max slice_s f (n-1) r1' in
      let all2 = seq_set_exact_chunk #_ #len r2' blocksize (n-1) (f (n-1) (seq_get_exact_chunk original_s blocksize (n-1))) in
      let _: squash (forall (i:nat{i < blocksize * (n - 1)}). Seq.index r1' i == Seq.index r2' i)
        = map_blocks_foldi_equiv_lemma len blocksize max (n - 1) original_s s f;
          assert ((forall (i:nat{i < blocksize * (n - 1)}). Seq.index r1' i == Seq.index r2' i))
      in
      map_blocks_foldi_preserves_lemma len blocksize max (n-1) original_s s f;
      map_blocks_f_equiv_lemma len blocksize max original_s f (n-1) r2' r1';
      assert (forall (j: nat{j < n * blocksize}). Seq.index all1 j == Seq.index all2 j);
      unfold_foldi_right 0 n (map_blocks_foldi_fun len blocksize max original_s f) s;
      LC.unfold_repeat_gen n (LSeq.map_blocks_a 'a blocksize max) (LSeq.map_blocks_f blocksize max slice_s f) Seq.empty (n - 1);
      ()
#pop-options
