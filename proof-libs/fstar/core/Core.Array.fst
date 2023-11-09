module Core.Array
open Rust_primitives

type t_TryFromSliceError = | TryFromSliceError

let impl_23__map n (arr: t_Array 'a n) (f: 'a -> 'b): t_Array 'b n 
  = map_array arr f
