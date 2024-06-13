module Core.Array
open Rust_primitives

type t_TryFromSliceError = | TryFromSliceError

let impl_23__map #a #b n (arr: t_Array a n) (f: a -> b): t_Array b n 
  = map_array arr f

let impl_23__as_slice #a len (arr: t_Array a len): t_Slice a = arr

let from_fn #a len (f: usize -> a): t_Array a len = admit()

