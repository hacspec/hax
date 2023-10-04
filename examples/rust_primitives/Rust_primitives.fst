module Rust_primitives

include Rust_primitives.Integers
include Rust_primitives.Arrays

class unsize_tc source = {
  output: Type;
  unsize: source -> output;
}


instance array_to_slice_unsize t n: unsize_tc (array t n) = {
  output = slice t;
  unsize = (fun (arr: array t n) -> arr);
}

