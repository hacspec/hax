module Rust_primitives

include Rust_primitives.Integers
include Rust_primitives.Arrays

class unsize_tc source = {
  output: Type;
  unsize: source -> output;
}

instance array_to_slice_unsize t n: unsize_tc (t_Array t n) = {
  output = t_Slice t;
  unsize = (fun (arr: t_Array t n) -> 
            arr <: t_Slice t);
}


