module Rust_primitives

include Rust_primitives.Integers
include Rust_primitives.Arrays

type t_Never = False
let never_to_any #t: t_Never -> t = (fun _ -> match () with)

class unsize_tc source = {
  output: Type;
  unsize: source -> output;
}


instance array_to_slice_unsize t n: unsize_tc (array t n) = {
  output = slice t;
  unsize = (fun (arr: array t n) -> 
            arr <: slice t);
}

