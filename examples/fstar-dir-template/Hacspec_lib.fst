module Hacspec_lib

include Hacspec.Lib

unfold type secret_t = uint32
unfold let update
  (#a: Type)
  (#len: uint_size)
  (s: lseq a len)
  (start: uint_size)
  (input: seq a {start + Seq.length input <= len})
    : lseq a len
  = array_update #a #len s start input 

unfold let len = seq_len

unfold type seq_t = seq

class has_default 'a = { def: 'a }

instance _: Hacspec_lib.has_default (Secret_integers.u8_t) = {
  def = secret (pub_u8 0)         
}

let new_ {| has_default 'a |} (len: uint_size) : lseq 'a len =
  Seq.create len def

// class new_seq_tc 'a = {
//   content: 'a;
//   new_: len:uint_size -> lseq 'a len;
// }

// instance new_seq_u8 a: new_seq_tc a = {
//   content = secret (pub_u8 0);
//   new_ = (fun len -> seq_new_ content)
// }

let num_exact_chunks = seq_num_exact_chunks
let get_exact_chunk = seq_get_exact_chunk

let set_exact_chunk 
  (#a: Type)
  (#len:uint_size) = seq_set_exact_chunk #a #len


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

unfold instance secret_uint_size: secret_tc uint_size = {
   int_type = U32;
   as_int = (fun (x: uint_size) -> x);
   secret = (fun x -> Hacspec.Lib.secret #U32 (pub_u32 x));
}

unfold let get_remainder_chunk = seq_get_remainder_chunk

unfold let set_chunk #a #len = seq_set_chunk #a #len

// let _ = assert (secret_t == int_t U32 SEC)

