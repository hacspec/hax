
module Core.Array
open Rust_primitives


open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST


inline_for_extraction
type t_TryFromSliceError = | TryFromSliceError

let impl_23__map n (arr: t_Array 'a n) (f: 'a -> 'b): t_Array 'b n  = admit()

inline_for_extraction
let impl_23__as_slice len (arr: t_Array 'a len): HST.St (t_Slice 'a) =
  {buffer = arr; len = len}
