module Core.Array
open Rust_primitives

let impl_23__map #n (arr: array 'a n) (f: 'a -> 'b): array 'b n 
  = map_array arr f
