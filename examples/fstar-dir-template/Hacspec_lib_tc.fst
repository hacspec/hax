module Hacspec_lib_tc

open FStar.Tactics.Typeclasses
open FStar.Mul
open Hacspec.Lib

class from_seq_tc (t: Type) 
  = { [@@@no_method] inner: Type
    ; [@@@no_method] size: nat
    ; from_seq: s:seq inner{seq_len s = size} -> t }
class has_new_ (o: Type) = {new_: o}

instance from_seq_lseq inner size: from_seq_tc (lseq inner size) 
  = { inner; size
    ; from_seq = array_from_seq size }

(*
class array_assign (o: Type0) 
  = { [@@@no_method] key: Type0
    ; [@@@no_method] value: Type0
    ; (.[]<-): o -> key -> value -> o }
instance array_lseq value (s: uint_size {s > 0}): array_assign (lseq value s)
  = { value; key = nat_mod s
    ; (.[]<-) = array_upd }
*)

class array_assign key (o: Type0) 
  = { [@@@no_method] value: Type0
     ;[@@@no_method] pred: key -> Type0
    ; (.[]<-): o -> k: key {pred k} -> value -> o }


instance array_assign_lseq_nat_mod value (s: uint_size {s > 0}): array_assign (nat_mod s) (lseq value s)
  = { value; pred = (fun _ -> True); (.[]<-) = array_upd }
  
instance array_assign_lseq_int value (s: uint_size {s > 0}): array_assign int (lseq value s)
  = { value; pred = (fun k -> k >= 0 /\ k < s); (.[]<-) = array_upd }

instance array_assign_lseq_nat value (s: uint_size {s > 0}): array_assign nat (lseq value s)
  = { value; pred = (fun (k: nat) -> k < s); (.[]<-) = array_upd }
  
instance array_assign_lseq_uint_size value (s: uint_size {s > 0}): array_assign uint_size (lseq value s)
  = { value; pred = (fun (k: uint_size) -> k >= 0 /\ k < s); (.[]<-) = array_upd }
  
instance array_assign_lseq_int32 value (s: uint_size {s > 0}): array_assign Int32.t (lseq value s)
  = { value; pred = (fun (k: Int32.t) -> v k >= 0 /\ v k < s)
    ; (.[]<-) = (fun s k -> array_upd s (Int32.v k)) }

class array_get key (o: Type0) 
  = { [@@@no_method] value: Type0
     ;[@@@no_method] pred: key -> Type0
    ; (.[]): o -> k: key {pred k} -> value }

instance array_get_lseq_nat_mod value (s: uint_size {s > 0}): array_get (nat_mod s) (lseq value s)
  = { value; pred = (fun _ -> True); (.[]) = array_index }
  
instance array_get_lseq_int value (s: uint_size {s > 0}): array_get int (lseq value s)
  = { value; pred = (fun k -> k >= 0 /\ k < s); (.[]) = array_index }

instance array_get_lseq_nat value (s: uint_size {s > 0}): array_get nat (lseq value s)
  = { value; pred = (fun (k: nat) -> k < s); (.[]) = array_index }
  
instance array_get_lseq_uint_size value (s: uint_size {s > 0}): array_get uint_size (lseq value s)
  = { value; pred = (fun (k: uint_size) -> k >= 0 /\ k < s); (.[]) = array_index }
  
instance array_get_lseq_int32 value (s: uint_size {s > 0}): array_get Int32.t (lseq value s)
  = { value; pred = (fun (k: Int32.t) -> v k >= 0 /\ v k < s)
    ; (.[]) = (fun s k -> array_index s (Int32.v k)) }

instance has_new_uint64: has_new_ uint64 = {new_ = secret (pub_u64 0)}
instance has_new_uint32: has_new_ uint32 = {new_ = secret (pub_u32 0)}
instance has_new_uint16: has_new_ uint16 = {new_ = secret (pub_u16 0)}
instance has_new_uint8: has_new_ uint8 = {new_ = secret (pub_u8 0)}
instance has_new_int64: has_new_ int64 = {new_ = secret (pub_i64 0)}
instance has_new_int32: has_new_ int32 = {new_ = secret (pub_i32 0)}
instance has_new_int16: has_new_ int16 = {new_ = secret (pub_i16 0)}
instance has_new_int8: has_new_ int8 = {new_ = secret (pub_i8 0)}

instance has_new_lseq {| has_new_ 'a |} s: has_new_ (lseq 'a s) 
  = {new_ = array_new_ new_ s}

let new_seq {| has_new_ 'a |} (len: uint_size) : lseq 'a len =
  Seq.create len new_

let to_le_bytes (#int_ty: inttype{unsigned int_ty /\ int_ty <> U1})
  (#len: uint_size{
    range (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16)) U32
  })
  = array_to_le_bytes #int_ty #len

let to_le_U32s = array_to_le_uint32s


class xor (t: Type) = { (^.): t -> t -> t }
instance xor_inherit t l: xor (int_t t l) = { (^.) = logxor }
instance xor_lseq (len: uint_size) (t:Type) {| xor t |}: xor (lseq t len) 
  = { (^.) = array_xor (^.) }

class mul (t: Type) = { ( *. ): t -> t -> t }
instance mul_inherit (t:inttype{unsigned t /\ ~(U128? t)}) l: mul (int_t t l) = { ( *. ) = mul_mod }
instance mul_nat_mod (m: pos): mul (nat_mod m) 
  = { ( *. ) = ( *% ) }
// instance mul_lseq (len: uint_size) (t:Type) {| mul t |}: mul (lseq t len) 
//   = { ( *. ) = array_xor ( *. ) }

class minus (t: Type) = { (-.): t -> t -> t }

instance _: minus int = { (-.) = (+) }
instance minus_inherit (t:inttype{unsigned t}) l: minus (int_t t l) = { (-.) = sub_mod }
// instance minus_lseq (len: uint_size) (t:Type) {| minus t |}: minus (lseq t len) 
//   = { (-.) = array_sub (-.) }

instance minus_nat_mod (m: pos): minus (nat_mod m)
  = { (-.) = (fun x y -> x +% y) }


class add (t: Type) = { (+.): t -> t -> t }

instance _: add int = { (+.) = (+) }
instance add_inherit (t:inttype{unsigned t}) l: add (int_t t l) = { (+.) = add_mod }
instance add_lseq (len: uint_size) (t:Type) {| add t |}: add (lseq t len) 
  = { (+.) = array_add (+.) }

instance add_nat_mod (m: pos): add (nat_mod m)
  = { (+.) = (fun x y -> x +% y) }


class bitor (t: Type) = { ( |. ): t -> t -> t }

// instance _: bitor int = { ( |. ) = ( Hacspec.Lib.( ( .| ) ) ) }
instance bitor_inherit (t:inttype{unsigned t}) l: bitor (int_t t l) = { ( |. ) = logor }
// instance bitor_lseq (len: uint_size) (t:Type) {| bitor t |}: bitor (lseq t len) 
//   = { ( |. ) = array_l ( |. ) }

// instance bitor_nat_mod (m: pos): bitor (nat_mod m)
//   = { ( |. ) = (fun x y -> x |. y) }

// let array_from_slice
//   (#a: Type)
//   (#default_value: a)
//   (#out_len: uint_size)
//   (input: seq a)
//   (start: uint_size)
//   (slice_len: uint_size{start + slice_len <= LSeq.length input /\ slice_len <= out_len})
//     : lseq a out_len
//   =
//   let out = LSeq.create out_len default_value in
  // LSeq.update_sub out 0 slice_len (LSeq.slice #a #(Seq.length input) input start (start + slice_len))

// unfold let to_byte_seq_le = nat_to_byte_seq_le


class from_byte_seq_le_tc len t = {
  [@@@no_method] n: pos;
  from_byte_seq_le: lseq uint8 len -> t
}

instance from_byte_seq_le_tc_ 
  (n: pos) (len: uint_size)
  : from_byte_seq_le_tc len (nat_mod n)
  = { n
    ; from_byte_seq_le = (fun x -> nat_from_byte_seq_le n len x) }

class from_literal_tc t = {
  [@@@no_method] m: pos;
  [@@@no_method] int_of_t: t -> int;
  from_literal: x:pub_uint128{v x < m} -> n:t{v x == int_of_t n}
}

instance from_literal_ (m: pos): from_literal_tc (nat_mod m) = {
  m;
  int_of_t = id;
  from_literal = (nat_from_literal m)
}

class to_byte_seq_le_tc t = {
  // [@@@no_method] n: pos;
  [@@@no_method] len: uint_size;
  to_byte_seq_le: #n:pos -> nat_mod n -> t
}

// TODO: simplify this
instance to_byte_seq_le_tc_ (len: uint_size)
                          : to_byte_seq_le_tc (lseq uint8 len)
  = { len;
      to_byte_seq_le = (fun #n x -> nat_to_byte_seq_le n len x)
    }

class from_slice_tc t = {
  [@@@no_method] inner: Type;
  [@@@no_method] out_len: uint_size;
  from_slice: input: seq inner 
            -> start: uint_size
            -> slice_len: uint_size{start + slice_len <= seq_len input /\ slice_len <= out_len}
            -> t
}

instance from_slice_tc_ 
  (inner: Type) (out_len: uint_size)
  {| has_new_ inner |}
  : from_slice_tc (lseq inner out_len)
  = { inner; out_len;
      from_slice = (fun input start (slice_len:uint_size{start + slice_len <= seq_len input /\ slice_len <= out_len}) ->
        array_from_slice #inner new_ out_len input start slice_len
      )
    }

let slice = array_slice

class has_zero t = {
  zero: t
}

instance _: has_zero int = {
  zero = 0
}

instance has_zero_nat_mod l: has_zero (nat_mod l) = {
  zero = 0
}

class secret_tc (t: Type) = {
  int_type: inttype;
  as_int: t -> int;
  secret: $x:t -> y:int_t int_type SEC{as_int x == v y}
}

unfold instance secret_uint_size_ref y: secret_tc (x:uint_size {x < y}) = {
   int_type = U32;
   as_int = (fun (x: uint_size {x < y}) -> x);
   secret = (fun x -> Hacspec.Lib.secret #U32 (pub_u32 x));
}


unfold instance secret_ul t: secret_tc (int_t t PUB) = {
   int_type = t;
   as_int = v;
   secret = (fun x -> Hacspec.Lib.secret #t x);
}

unfold instance secret_U32: secret_tc uint_size = {
   int_type = U32;
   as_int = (fun (x: uint_size) -> x);
   secret = (fun x -> Hacspec.Lib.secret #U32 (pub_u32 x));
}

unfold instance secret_U128: secret_tc pub_uint128 = {
   int_type = U128;
   as_int = (fun (x: pub_uint128) -> v x);
   secret = (fun x -> Hacspec.Lib.secret #U128 x);
}

unfold instance secret_U8: secret_tc pub_uint8 = {
   int_type = U8;
   as_int = (fun (x: pub_uint8) -> v x);
   secret = (fun x -> Hacspec.Lib.secret #U8 x);
}


unfold instance secret_U128' pred: secret_tc (x:pub_uint128{pred x}) = {
   int_type = U128;
   as_int = (fun (x: pub_uint128{pred x}) -> v x);
   secret = (fun x -> Hacspec.Lib.secret #U128 x);
}


let from_secret_literal (#m:pos) = nat_from_secret_literal m


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

unfold let update #a #len = array_update #a #len
unfold let update_start #a #len s = array_update #a #len s 0
unfold type seq_t = seq
unfold let len = seq_len
unfold let num_exact_chunks = seq_num_exact_chunks
unfold let get_exact_chunk = seq_get_exact_chunk
unfold let set_exact_chunk #a #len = seq_set_exact_chunk #a #len
unfold let get_remainder_chunk = seq_get_remainder_chunk
unfold let set_chunk #a #len = seq_set_chunk #a #len
unfold let uint128_from_le_bytes = uint128_from_le_bytes
unfold let u128_to_le_bytes = uint128_to_le_bytes
unfold let inv #n = nat_inv n
unfold let pow #m = nat_pow m
unfold let bit #m = nat_bit m
