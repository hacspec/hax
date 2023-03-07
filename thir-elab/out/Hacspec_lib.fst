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

