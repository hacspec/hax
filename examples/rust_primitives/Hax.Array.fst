module Hax.Array
open Core.Types
  
let repeat (x: 'a) (len: usize): array 'a len = 
  FStar.Seq.create (SizeT.v len) x
  
