module Rust_primitives

include Rust_primitives.Integers
include Rust_primitives.Arrays

class cast_tc a b = {
  cast: a -> b; 
}

/// Rust's casts operations on integers are non-panicking
instance cast_tc_integers (t:inttype) (t':inttype)
  : cast_tc (int_t t) (int_t t')
  = { cast = (fun x -> Rust_primitives.Integers.cast_mod #t #t' x) }

class unsize_tc source = {
  output: Type;
  unsize: source -> output;
}

instance array_to_slice_unsize t n: unsize_tc (t_Array t n) = {
  output = t_Slice t;
  unsize = (fun (arr: t_Array t n) -> 
            arr <: t_Slice t);
}


