module Hacspec.Lib

open FStar.Mul

(*** Integers *)

include Lib.IntTypes

(**** Usize  *)

let uint_size = range_t U32
let int_size = range_t S32

unfold
let usize (n:range_t U32) : u:uint_size{u == n} = n

unfold
let isize (n:range_t S32) : u:int_size{u == n} = n

(**** Public integers *)

unfold
let pub_u8 (n:range_t U8) : u:pub_uint8{v u == n} = uint #U8 #PUB n

unfold
let pub_i8 (n:range_t S8) : u:pub_int8{v u == n} = sint #S8 #PUB n

unfold
let pub_u16 (n:range_t U16) : u:pub_uint16{v u == n} = uint #U16 #PUB n

unfold
let pub_i16 (n:range_t S16) : u:pub_int16{v u == n} = sint #S16 #PUB n

unfold
let pub_u32 (n:range_t U32) : u:pub_uint32{v u == n} = uint #U32 #PUB n

unfold
let pub_i32 (n:range_t S32) : u:pub_int32{v u == n} = sint #S32 #PUB n

unfold
let pub_u64 (n:range_t U64) : u:pub_uint64{v u == n} = uint #U64 #PUB n

unfold
let pub_i64 (n:range_t S64) : u:pub_int64{v u == n} = sint #S64 #PUB n

unfold
let pub_u128 (n:range_t U128) : u:pub_uint128{v u == n} = uint #U128 #PUB n

unfold
let pub_i128 (n:range_t S128) : u:pub_int128{v u == n} = sint #S128 #PUB n

(**** Operations *)

let uint8_rotate_left (u: uint8) (s: uint_size{s > 0 /\ s < 8}) : uint8 =
  rotate_left u (size s)

let uint8_rotate_right (u: uint8) (s: uint_size{s > 0 /\ s < 8}) : uint8 =
  rotate_right u (size s)

let uint16_rotate_left (u: uint16) (s: uint_size{s > 0 /\ s < 16}) : uint16 =
  rotate_left u (size s)

let uint16_rotate_right (u: uint16) (s: uint_size{s > 0 /\ s < 16}) : uint16 =
  rotate_right u (size s)

let uint32_rotate_left (u: uint32) (s: uint_size{s > 0 /\ s < 32}) : uint32 =
  rotate_left u (size s)

let uint32_rotate_right (u: uint32) (s: uint_size{s > 0 /\ s < 32}) : uint32 =
  rotate_right u (size s)

let uint64_rotate_left (u: uint64) (s: uint_size{s > 0 /\ s < 64}) : uint64 =
  rotate_left u (size s)

let uint64_rotate_right (u: uint64) (s: uint_size{s > 0 /\ s < 64}) : uint64 =
  rotate_right u (size s)

let uint128_rotate_left (u: uint128) (s: uint_size{s > 0 /\ s < 128}) : uint128 =
  rotate_left u (size s)

let uint128_rotate_right (u: uint128) (s: uint_size{s > 0 /\ s < 128}) : uint128 =
  rotate_right u (size s)

let usize_shift_right (u: uint_size) (s: pub_uint32{v s < 32}) : uint_size =
  v (shift_right (size u) s)

let usize_shift_left (u: uint_size) (s: pub_uint32{v s < 32}) : uint_size =
  v (shift_left (size u) s)

let usize_bit_and (u: uint_size) (s: uint_size) : uint_size =
  v ((size u) &. (size s))

let pub_uint128_wrapping_add (x y: pub_uint128) : pub_uint128 =
  x +. y

let pub_uint32_leading_zeros (x: pub_uint32) : pub_uint32 =
  admit()

let pub_uint32_clone(x: pub_uint32) : pub_uint32 =
  x

(*** Option *)

let option_unwrap (#a: Type) (x: option a{Some? x}) : a =
  Some?.v x


(*** Result *)

type result (a: Type) (b: Type) =
  | Ok : a -> result a b
  | Err : b -> result a b

let bind_ok (#a #a' #b: Type) (v: result a b) (kont: a -> result a' b) : result a' b =
   match v with
   | Ok x -> kont x
   | Err y -> Err y

let (let?) = bind_ok

(*** Loops *)

let fold
  (#acc: Type)
  (hi: uint_size)
  (f: (acc -> acc))
  (init: acc)
    : acc
  =
  Lib.LoopCombinators.repeat hi f init

val fold_extensionality
  (#acc: Type)
  (hi: uint_size)
  (f: (acc -> acc))
  (g: (acc -> acc))
  (init: acc)
    : Lemma (requires (forall a. f a == g a))
            (ensures (fold #acc hi f init == fold #acc hi g init))

let fold_extensionality #acc hi f g init = admit()

let foldi0
  (#acc: Type)
  (hi: uint_size)
  (f: (i:uint_size{i < hi} -> acc -> acc))
  (init: acc)
    : acc
  =
  Lib.LoopCombinators.repeati hi f init


let rec foldi
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (init: 'a)
  : Tot 'a (decreases (hi - lo))
  = if lo = hi then init
               else foldi (lo+1) hi f (f lo init)

let foldi_equiv_repeat_right
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (init: 'a)
  : Lemma (foldi lo hi f init == Lib.LoopCombinators.repeat_right lo hi (Lib.LoopCombinators.fixed_a 'a) f init)
  = admit ()

let unfold_foldi_right
  (lo: uint_size)
  (hi: uint_size{lo < hi})
  (f: (i:uint_size{i < hi}) -> 'a -> 'a)
  (init: 'a)
  : Lemma (foldi lo hi f init == f (hi - 1) (foldi lo (hi - 1) f init))
  = foldi_equiv_repeat_right lo hi f init;
    Lib.LoopCombinators.unfold_repeat_right lo hi (Lib.LoopCombinators.fixed_a 'a) f init (hi - 1);
    foldi_equiv_repeat_right lo (hi-1) f init

let unfold_foldi (lo: uint_size) (hi: uint_size{lo <= hi})
                 (f: (i:uint_size{i < hi}) -> 'a -> 'a)
                 (init: 'a)
  : Lemma (foldi lo hi f init == (if lo = hi then init else
                                 foldi (lo + 1) hi f (f lo init)))
  = assert_norm ((foldi lo hi f init == (if lo = hi then init else
                                 foldi (lo + 1) hi f (f lo init))))

let rec foldi_result_
  (#acc_ok: Type)
  (#err: Type)
  (cur_i: uint_size)
  (hi: uint_size{cur_i <= hi})
  (f: (i:uint_size{i < hi}) -> acc_ok -> (result acc_ok err))
  (cur: acc_ok)
    : Tot (result acc_ok err) (decreases (hi - cur_i))
  =
  if cur_i = hi then Ok cur else
  match f cur_i cur with
  | Err x -> Err x
  | Ok y -> foldi_result_ (cur_i + 1) hi f y

let foldi_result
  (#acc_ok: Type)
  (#err: Type)
  (lo: uint_size)
  (hi: uint_size{lo <= hi})
  (f: (i:uint_size{i < hi}) -> acc_ok -> (result acc_ok err))
  (init: acc_ok)
    : result acc_ok err
  =
  foldi_result_ lo hi f init

(*** Seq *)

module LSeq = Lib.Sequence
module LBSeq = Lib.ByteSequence

let lseq (a: Type) (len: uint_size) = LSeq.lseq a len

let seq (a: Type) = s:LSeq.seq a{range (LSeq.length s) U32}

unfold let byte_seq = seq uint8

let nseq (a: Type) (len: nat) = s:LSeq.seq a{LSeq.length s == len}

let seq_len (#a: Type) (s: seq a) : nat = Seq.length s

let seq_new_ (#a: Type) (init:a) (len: uint_size) : lseq a len =
  Seq.create len init

let seq_clone (#a: Type) (s: seq a) : seq a = s

let seq_index (#a: Type) (s: seq a) (i: uint_size{i < seq_len s}) : a =
  Seq.index s i

let seq_upd (#a: Type) (s: seq a) (i: uint_size{i < seq_len s}) (new_v: a)
    : (s':seq a{seq_len s' = seq_len s})  =
  Seq.upd s i new_v

let seq_update_start
  (#a: Type)
  (s: seq a)
  (start_s: seq a{Seq.length start_s <= Seq.length s})
    : seq a
  =
  LSeq.update_sub #_ #(Seq.length s) s 0 (Seq.length start_s) start_s

let seq_from_seq (#a: Type) (s: seq a) : seq a = s


(**** Array manipulation *)

let array_new_ (#a: Type) (init:a) (len: uint_size)  : lseq a len =
  LSeq.create len init

let array_from_list
  (#a: Type)
  (l: list a{List.Tot.length l <= max_size_t})
    : lseq a (List.Tot.length l)
  =
  LSeq.of_list l

let array_index (#a: Type) (#len:uint_size) (s: lseq a len) (i: uint_size{i < len}) : a =
  LSeq.index s i

let op_String_Access #a #len s i = array_index #a #len s i

let array_upd (#a: Type) (#len:uint_size) (s: lseq a len) (i: uint_size{i < len}) (new_v: a) : lseq a len = LSeq.upd s i new_v

let array_from_seq
  (#a: Type)
  (out_len:uint_size)
  (input: seq a{Seq.length input = out_len})
    : lseq a out_len
  = input

let array_update
  (#a: Type)
  (#len: uint_size)
  (s: lseq a len)
  (start: uint_size)
  (input: seq a {start + Seq.length input <= len})
    : lseq a len
  =
  LSeq.update_sub #a #(LSeq.length s) s start (LSeq.length input) input

let array_from_slice
  (#a: Type)
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <= LSeq.length input /\ slice_len <= out_len})
    : lseq a out_len
  =
  let out = LSeq.create out_len default_value in
  LSeq.update_sub out 0 slice_len (LSeq.slice #a #(Seq.length input) input start (start + slice_len))

let array_slice
  (#a: Type)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <= LSeq.length input})
    : lseq a slice_len
  =
  Seq.slice input start (start + slice_len)

let array_from_slice_range
  (#a: Type)
  (default_value: a)
  (out_len: uint_size)
  (input: seq a)
  (start_fin: (uint_size & uint_size){
     fst start_fin >= 0 /\ snd start_fin <= LSeq.length input /\ snd start_fin >= fst start_fin /\
     snd start_fin - fst start_fin <= out_len
   })
    : lseq a out_len
  =
  let out = array_new_ default_value out_len in
  let (start, fin) = start_fin in
  LSeq.update_sub out 0 (fin - start) (Seq.slice input start fin)

let array_slice_range
  (#a: Type)
  (#len:uint_size)
  (input: lseq a len)
  (start_fin:(uint_size & uint_size){
    fst start_fin >= 0 /\ snd start_fin <= len /\ snd start_fin >= fst start_fin
  })
    : lseq a (snd start_fin - fst start_fin)
  =
  let (start, fin) = start_fin in
  LSeq.slice input start fin

let array_update_start
  (#a: Type)
  (#len: uint_size)
  (s: lseq a len)
  (start_s: seq a{Seq.length start_s <= len})
    : lseq a len
  =
  LSeq.update_sub s 0 (Seq.length start_s) start_s

let array_len  (#a: Type) (#len: uint_size) (s: lseq a len) = len


//TODO
let array_to_le_uint32s (s:seq uint8{4 * seq_len s < pow2 32 /\ seq_len s % 4 = 0}) : seq uint32 =
    let ulen : size_nat = seq_len s / 4 in
    let s : lseq uint8 (4*ulen) = LSeq.to_lseq s in
    Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #ulen s

let array_to_be_uint32s (#len: uint_size) (s: lseq uint8 len{len % 4 = 0}) : lseq uint32 (len / 4) =
  admit()

let array_to_le_bytes
  (#int_ty: inttype{unsigned int_ty /\ int_ty <> U1})
  (#len: uint_size{
    range (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16)) U32
  })
  (s: lseq (uint_t int_ty SEC) len)
    : lseq uint8 (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16))
  = Lib.ByteSequence.uints_to_bytes_le s

let array_to_be_bytes
  (#int_ty: inttype{unsigned int_ty /\ int_ty <> U1})
  (#len: uint_size{
    range (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16)) U32
  })
  (s: lseq (uint_t int_ty SEC) len)
    : lseq uint8 (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16))
  = Lib.ByteSequence.uints_to_bytes_be s

let array_declassify_eq (#a: eqtype) (#len: uint_size) (x y: lseq a len) : bool =
  Seq.Properties.for_all (fun (x, y) -> x = y) (Lib.Sequence.map2 (fun x y -> (x,y)) x y)

(**** Seq manipulation *)

let seq_slice
  (#a: Type)
  (s: seq a)
  (start: uint_size)
  (len: uint_size{start + len <= LSeq.length s})
    : lseq a len
  =
  LSeq.slice #a #(Seq.length s) s start (start + len)

let seq_update
  (#a: Type)
  (s: seq a)
  (start: uint_size)
  (input: seq a{start + LSeq.length input <= LSeq.length s})
    : nseq a (LSeq.length s)
  =
  LSeq.update_sub #a #(LSeq.length s) s start (LSeq.length input) input

let seq_update_slice
  (#a: Type)
  (out: seq a)
  (start_out: uint_size)
  (input: seq a)
  (start_in: uint_size)
  (len: uint_size{
    start_in + len <= LSeq.length input /\
    start_out + len <= LSeq.length out
  })
    : nseq a (LSeq.length out)
  =
  LSeq.update_sub #a #(LSeq.length out) out start_out len
    (LSeq.sub #a #(LSeq.length input) input start_in len)

let seq_concat
  (#a: Type)
  (s1 :seq a)
  (s2: seq a{range (LSeq.length s1 + LSeq.length s2) U32})
  : lseq a (LSeq.length s1 + LSeq.length s2)
  =
  LSeq.concat #a #(LSeq.length s1) #(LSeq.length s2) s1 s2


(**** Chunking *)

let seq_num_chunks (#a: Type) (s: seq a) (chunk_len: uint_size{chunk_len > 0}) : uint_size =
  (Seq.length s + chunk_len - 1) / chunk_len

let seq_num_exact_chunks
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size{chunk_len > 0})
    : uint_size =
  Seq.length s / chunk_len

let seq_chunk_len
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size{chunk_len * chunk_num <= Seq.length s})
    : Tot (out_len:uint_size{out_len <= chunk_len})
  =
  let idx_start = chunk_len * chunk_num in
  if idx_start + chunk_len > Seq.length s then
    Seq.length s - idx_start
  else
    chunk_len

let seq_chunk_same_len_same_chunk_len
  (#a: Type)
  (s1 s2: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Lemma
    (requires (LSeq.length s1 = LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_num = seq_chunk_len s2 chunk_len chunk_num))
    [SMTPat (seq_chunk_len s1 chunk_len chunk_num); SMTPat (seq_chunk_len s2 chunk_len chunk_num)]
  =
  ()

let seq_get_chunk
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Pure (uint_size & seq a)
    (requires (chunk_len * chunk_num <= Seq.length s))
    (ensures (fun (out_len, chunk) ->
      out_len = seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk = out_len
    ))
  =
  let idx_start = chunk_len * chunk_num in
  let out_len = seq_chunk_len s chunk_len chunk_num in
  (out_len, LSeq.slice #a #(Seq.length s)
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num))

let seq_get_exact_chunk
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Pure (lseq a chunk_len)
    (requires (chunk_len * (chunk_num + 1) <= Seq.length s))
    (ensures (fun chunk -> True))
  =
  snd (seq_get_chunk s chunk_len chunk_num)

let seq_get_remainder_chunk
  (s: seq 'a) (chunk_len: uint_size{chunk_len > 0}): seq 'a
  = let chunks = seq_num_chunks s chunk_len in
    let last_chunk = if chunks > 0 then chunks - 1 else 0 in
    let (len, chunk) = seq_get_chunk s chunk_len last_chunk in
    if len = chunk_len then Seq.empty else chunk

// let seq_get_remainder_chunk_length_lemma (inp:seq 'a) (blocksize:size_pos)
//   : Lemma (length (seq_get_remainder_chunk inp blocksize) == length inp % blocksize)
//   = let r = seq_get_remainder_chunk inp blocksize in
//     let chunks = seq_num_chunks inp blocksize in
//     let last_chunk = if chunks > 0 then chunks - 1 else 0 in
//     assert (seq_chunk_len inp blocksize last_chunk == (
//       if blocksize * (last_chunk + 1) > length inp
//       then (if blocksize * last_chunk < length inp
//             then sub_rem_lemma last_chunk (length inp) blocksize;
//             length inp % blocksize)
//       else blocksize
//     ));
//     let (_, chunk) = seq_get_chunk inp blocksize last_chunk in
//     if length chunk = blocksize
//     then Math.Lemmas.cancel_mul_mod (last_chunk + 1) blocksize

let seq_set_chunk
  (#a: Type)
  (#len:uint_size) (* change to nseq but update_sub missing for nseq *)
  (s: lseq a len)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: seq a)
    : Pure (lseq a len)
      (requires (
        chunk_len * chunk_num <= Seq.length s /\
        LSeq.length chunk = seq_chunk_len s chunk_len chunk_num
      ))
      (ensures (fun out -> True))
  =
  let idx_start = chunk_len * chunk_num in
  let out_len = seq_chunk_len s chunk_len chunk_num in
  LSeq.update_sub s idx_start out_len chunk

let seq_set_exact_chunk
  (#a: Type)
  (#len:uint_size) (* change to nseq but update_sub missing for nseq *)
  (s: lseq a len)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: seq a )
    : Pure (lseq a len)
      (requires (
        chunk_len * (chunk_num + 1) <= Seq.length s /\
        LSeq.length chunk = seq_chunk_len s chunk_len chunk_num
      ))
      (ensures (fun out -> True))
  =
  seq_set_chunk s chunk_len chunk_num chunk


(**** Numeric operations *)

let array_add (#len: uint_size)
              (add: 'a -> 'a -> 'a)
              (s1 s2: lseq 'a len)
              : lseq 'a len
  = LSeq.map2 add s1 s2

let array_xor (#len: uint_size)
              (xor: 'a -> 'a -> 'a)
              (s1 s2: lseq 'a len)
              : lseq 'a len
  = LSeq.map2 xor s1 s2

let array_eq
  (#a: Type)
  (#len: uint_size)
  (eq: a -> a -> bool)
  (s1: lseq a len)
  (s2 : lseq a len)
    : bool
  = 
  let out = true in
  foldi 0 len (fun i out ->
    out && (array_index s1 i `eq` array_index s2 i)
  ) out

(**** Integers to arrays *)

let uint16_to_le_bytes (x: uint16) : lseq uint8 2 =
  LBSeq.uint_to_bytes_le x

let uint16_to_be_bytes (x: uint16) : lseq uint8 2 =
  LBSeq.uint_to_bytes_be x

let uint16_from_le_bytes (s: lseq uint8 2) : uint16 =
  LBSeq.uint_from_bytes_le s

let uint16_from_be_bytes (s: lseq uint8 2) : uint16 =
  LBSeq.uint_from_bytes_be s

let uint32_to_le_bytes (x: uint32) : lseq uint8 4 =
  LBSeq.uint_to_bytes_le x

let uint32_to_be_bytes (x: uint32) : lseq uint8 4 =
  LBSeq.uint_to_bytes_be x

let uint32_from_le_bytes (s: lseq uint8 4) : uint32 =
  LBSeq.uint_from_bytes_le s

let uint32_from_be_bytes (s: lseq uint8 4) : uint32 =
  LBSeq.uint_from_bytes_be s

let uint64_to_le_bytes (x: uint64) : lseq uint8 8 =
  LBSeq.uint_to_bytes_le x

let uint64_to_be_bytes (x: uint64) : lseq uint8 8 =
  LBSeq.uint_to_bytes_be x

let uint64_from_le_bytes (s: lseq uint8 8) : uint64 =
  LBSeq.uint_from_bytes_le s

let uint64_from_be_bytes (s: lseq uint8 8) : uint64 =
  LBSeq.uint_from_bytes_be s

let uint128_to_le_bytes (x: uint128) : lseq uint8 16 =
  LBSeq.uint_to_bytes_le x

let uint128_to_be_bytes (x: uint128) : lseq uint8 16 =
  LBSeq.uint_to_bytes_be x

let uint128_from_le_bytes (input: lseq uint8 16) : uint128 =
  LBSeq.uint_from_bytes_le input

let uint128_from_be_bytes (s: lseq uint8 16) : uint128 =
  LBSeq.uint_from_bytes_be s


let u16_to_le_bytes (x: pub_uint16) : lseq pub_uint8 2 =
  LBSeq.uint_to_bytes_le x

let u16_to_be_bytes (x: pub_uint16) : lseq pub_uint8 2 =
  LBSeq.uint_to_bytes_be x

let u16_from_le_bytes (s: lseq pub_uint8 2) : pub_uint16 =
  LBSeq.uint_from_bytes_le s

let u16_from_be_bytes (s: lseq pub_uint8 2) : pub_uint16 =
  LBSeq.uint_from_bytes_be s

let u32_to_le_bytes (x: pub_uint32) : lseq pub_uint8 4 =
  LBSeq.uint_to_bytes_le x

let u32_to_be_bytes (x: pub_uint32) : lseq pub_uint8 4 =
  LBSeq.uint_to_bytes_be x

let u32_from_le_bytes (s: lseq pub_uint8 4) : pub_uint32 =
  LBSeq.uint_from_bytes_le s

let u32_from_be_bytes (s: lseq pub_uint8 4) : pub_uint32 =
  LBSeq.uint_from_bytes_be s

let u64_to_le_bytes (x: pub_uint64) : lseq pub_uint8 8 =
  LBSeq.uint_to_bytes_le x

let u64_to_be_bytes (x: pub_uint64) : lseq pub_uint8 8 =
  LBSeq.uint_to_bytes_be x

let u64_from_le_bytes (s: lseq pub_uint8 8) : pub_uint64 =
  LBSeq.uint_from_bytes_le s

let u64_from_be_bytes (s: lseq pub_uint8 8) : pub_uint64 =
  LBSeq.uint_from_bytes_be s

let u128_to_le_bytes (x: pub_uint128) : lseq pub_uint8 16 =
  LBSeq.uint_to_bytes_le x

let u128_to_be_bytes (x: pub_uint128) : lseq pub_uint8 16 =
  LBSeq.uint_to_bytes_be x

let u128_from_le_bytes (input: lseq pub_uint8 16) : pub_uint128 =
  LBSeq.uint_from_bytes_le input

let u128_from_be_bytes (s: lseq pub_uint8 16) : pub_uint128 =
  LBSeq.uint_from_bytes_be s

(**** Casting *)

let uint32_from_uint8 (x: uint8) : uint32 = cast U32 SEC x

let uint64_from_uint8 (x: uint8) : uint64 = cast U64 SEC x

let uint8_from_uint64 (x: uint64) : uint8 = cast U8 SEC x


(**** Declassification *)

let uint32_declassify (x: uint32) : pub_uint32 = uint (Lib.RawIntTypes.uint_to_nat x)

(**** Classification *)

let uint64_classify (x: pub_uint64) : uint64 = uint (Lib.RawIntTypes.uint_to_nat x)

(*** Nats *)
let less_eq (x:nat) (y:nat) = x <= y

let nat_mod (n: pos) = x:nat{x < n}

val (+%) (#n:pos) (a:nat_mod n) (b:nat_mod n) : nat_mod n
let (+%) #n a b = (a + b) % n

val (-%) (#n:pos) (a:nat_mod n) (b:nat_mod n) : nat_mod n
let (-%) #n a b = (a - b) % n


val ( *% ) (#n:pos) (a:nat_mod n) (b:nat_mod n) : nat_mod n
let ( *% ) #n a b = (a * b) % n

let nat_exp (m: pos) (n: nat_mod m) (exponent: pub_uint32) : nat_mod m =
  admit()

let nat_inv (m: pos) (n: nat_mod m) : nat_mod m =
  admit()

let nat_one (m: pos) : nat_mod m = 1 % m

let nat_pow2 (m:pos) (x: nat{pow2 x < m}) : nat_mod m = pow2 x

let nat_pow (m: pos) (x: nat_mod m) (exponent: pub_uint128) : nat_mod m =
  admit()

let nat_zero (m: pos) : nat_mod m = 0


let nat_equal (m: pos) (n n': nat_mod m) : bool = n = n'

let nat_get_bit (m: pos) (n: nat_mod m) (bit: uint_size) : nat_mod m =
  admit()

let nat_bit (m: pos) (n: nat_mod m) (bit: uint_size) : bool =
  admit()


let nat_from_secret_literal (m:pos) (x:uint128{v x < m}) : n:nat_mod m{v x == n} =
  v x

let nat_from_literal (m: pos) (x:pub_uint128{v x < m}) : n:nat_mod m{v x == n} =
  v x

let nat_to_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq uint8 len =
  let n' = n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n'


let nat_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  let n' = x % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_le len n'

let nat_to_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod n) : lseq uint8 len =
  let n' = x % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_le len n'

let nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  let n' = x % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n'

let nat_from_byte_seq_be (n : pos) (len: uint_size) (x: lseq uint8 len) : nat_mod n =
  let out = Lib.ByteSequence.nat_from_bytes_be x in
  admit();
  out

let nat_from_byte_seq_le (n : pos) (len: uint_size) (x: lseq uint8 len) : nat_mod n =
  let out = Lib.ByteSequence.nat_from_bytes_be x in
  admit();
  out

(**** Math utils *)

let mul_poly_irr
  (#t: inttype)
  (#l: secrecy_level)
  (a b irr: seq (int_t t l))
  (modulo: int_t t l) : seq (int_t t l) =
    admit()

let add_poly
  (#t: inttype)
  (#l: secrecy_level)
  (a b: seq (int_t t l))
  (modulo: int_t t l) : seq (int_t t l) =
    admit()

let poly_to_ring
  (#t: inttype)
  (#l: secrecy_level)
  (irr poly: seq (int_t t l))
  (modulo: int_t t l) : seq (int_t t l) & bool =
    admit()

let make_positive
  (#t: inttype)
  (#l: secrecy_level)
  (poly: seq (int_t t l))
  (q: int_t t l) : seq (int_t t l) =
    admit()

(* Math lemmas *)

val add_mod_associativity: #t:inttype{unsigned t} -> #l:secrecy_level -> a:uint_t t l -> b:uint_t t l -> c:uint_t t l
  -> Lemma (a +. b +. c == a +. (b +. c))
    [SMTPat (a +. b +. c)]

let add_mod_associativity a b c =
  assume (v (a+.b+.c) == v (a +. (b +. c)))

val logand_uint64_uint128 (a a' b b': UInt.uint_t 64)
  : Lemma (UInt.logand #128 (a + pow2 64 * b) (a' + pow2 64 * b') == UInt.logand #64 a a' + pow2 64 * UInt.logand #64 b b')

let logand_uint64_uint128 a a' b b' = admit()

val pow2_le_compat: m:nat -> n:nat -> Lemma
  (requires (m <= n))
  (ensures  (pow2 m `less_eq` pow2 n))
  [SMTPat (pow2 m `less_eq` pow2 n)]

let pow2_le_compat m n = Math.Lemmas.pow2_le_compat n m

val nat_from_zero_bytes (#len:size_nat) (b:Lib.ByteSequence.lbytes len)
  : Lemma (requires (forall i. v b.[i] == 0))
          (ensures (Lib.ByteSequence.nat_from_bytes_le b == 0))
let nat_from_zero_bytes #len b = admit()

let expand_subtraction (a b d: int): Lemma ((a - b) * d == a * d - b * d) = ()
let division_order_lemma_ge (a b:nat) (d:pos): Lemma (requires a >= b) (ensures a/d >= b/d)
  = let ka, kb = a/d, b/d in
    Math.Lemmas.euclidean_division_definition a d;
    Math.Lemmas.euclidean_division_definition b d;
    if ka < kb then expand_subtraction kb ka d else ()

let division_order_lemma_gt (a b:nat) (d:pos): Lemma (requires a > b) (ensures a/d >= b/d)
  = division_order_lemma_ge a b d


/// if [a·k < b < (a+1)·k], then [b - a·k == b % k]
let framed_mod_lemma (a b: nat) (k: pos)
  : Lemma (requires a * k < b 
                          /\ b < (a + 1) * k)
          (ensures  b - a * k == b % k)
  = let kb, rb = b / k, b % k in
    Math.Lemmas.euclidean_division_definition b k;
    Math.Lemmas.small_div rb k;
    if kb > a then division_order_lemma_gt (a + 1) (kb * k + rb) k
    else if kb < a then (division_order_lemma_gt (k * kb + rb) (a * k) k;
                         Math.Lemmas.cancel_mul_div  a k;      
                         Math.Lemmas.cancel_mul_div kb k)

