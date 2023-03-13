module Hacspec_chacha20.Header

open FStar.Mul
open Hacspec.Lib

type state_t = lseq (uint32) (16)

let state_idx =
  nat_mod (16)

type constants_t = lseq (uint32) (4)

let constants_idx =
  nat_mod (4)

type block_t = lseq (uint8) (64)

type chaChaIV_t = lseq (uint8) (12)

type chaChaKey_t = lseq (uint8) (32)

let x = 3l

class from_seq_tc (t: Type) = {
  inner: Type;
  size: nat;
  from_seq: s:seq inner{seq_len s = size} -> t
}

instance _: from_seq_tc state_t = {
  inner = uint32;
  size = 16;
  from_seq = array_from_seq 16
}

instance _: from_seq_tc block_t = {
  inner = uint8;
  size = 64;
  from_seq = array_from_seq 64
}

let to_le_bytes (#int_ty: inttype{unsigned int_ty /\ int_ty <> U1})
  (#len: uint_size{
    range (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16)) U32
  })
  = array_to_le_bytes #int_ty #len

let to_le_U32s = array_to_le_uint32s

class array_assign (o: Type0) = {
  key: Type0;
  value: Type0;
  (.[]<-): o -> key -> value -> o
}

instance array_upd1: array_assign state_t = {
  key = state_idx;
  value = uint32;
  (.[]<-) = array_upd
}

instance array_upd2: array_assign constants_t = {
  key = constants_idx;
  value = uint32;
  (.[]<-) = array_upd
}
class has_default (o: Type) = {new_: o}
instance _: has_default state_t = {new_ = array_new_ (secret 0x0ul) 16}
instance _: has_default constants_t = {new_ = array_new_ (secret 0x0ul) 4}
instance _: has_default block_t = {new_ = array_new_ (secret (pub_u8 0x0)) 64}

class xor (t: Type) = { (^.): t -> t -> t }
instance xor_inherit t l: xor (int_t t l) = { (^.) = logxor }
instance xor_lseq (len: uint_size) (t:Type) {| xor t |}: xor (lseq t len) 
  = { (^.) = array_xor (^.) }

class add (t: Type) = { (+.): t -> t -> t }

instance _: add int = { (+.) = (+) }
instance add_inherit (t:inttype{unsigned t}) l: add (int_t t l) = { (+.) = add_mod }
instance add_lseq (len: uint_size) (t:Type) {| add t |}: add (lseq t len) 
  = { (+.) = array_add (+.) }

let slice = array_slice




// class foldi_tc (key: eqtype) = {
//   foldi_lt_key: key -> key -> bool;
//   pred: key -> Type;
//   foldi: (#a: Type) -> 
//          (lo: key {pred lo}) ->
//          (hi: key{pred hi /\ lo `foldi_lt_key` hi \/ lo == hi}) ->
//          (f: (i:key{pred i /\ i `foldi_lt_key` hi}) -> a -> a) ->
//          (init: a) -> a
// }

// unfold instance foldi_int: foldi_tc int = {
//   foldi_lt_key = (<=);
//   pred = (fun x -> range x U32);
//   foldi = Hacspec.Lib.foldi
// }
// unfold instance foldi_range_t_u32: foldi_tc (range_t U32) = {
//   foldi_lt_key = (<=);
//   pred = (fun x -> True);
//   foldi = Hacspec.Lib.foldi
// }
// unfold instance _: foldi_tc Int32.t =
//   let foldi_lt_key = (fun x y -> Int32.lt x y) in
//   let pred = (fun x -> range (Int32.v x) U32) in
//   let foldi (#a: Type)
//          (lo: Int32.t {pred lo})
//          (hi: Int32.t{pred hi /\ lo `foldi_lt_key` hi \/ lo == hi})
//          (f: (i:Int32.t{pred i /\ i `foldi_lt_key` hi}) -> a -> a)
//          (init: a) = 
//            Hacspec.Lib.foldi #a (Int32.v lo) (Int32.v hi) 
//                                      (fun i -> f (Int32.int_to_t i)) init
//          in
//   {
//   foldi_lt_key;
//   pred;
//   foldi
// }
