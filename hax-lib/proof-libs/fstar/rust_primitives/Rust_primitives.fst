module Rust_primitives

include Rust_primitives.Integers
include Rust_primitives.Arrays
include Rust_primitives.BitVectors
include Rust_primitives.Float
include Rust_primitives.Char

class cast_tc a b = {
  cast: a -> b; 
}

/// Rust's casts operations on integers are non-panicking
instance cast_tc_integers (t:inttype) (t':inttype)
  : cast_tc (int_t t) (int_t t')
  = { cast = (fun x -> Rust_primitives.Integers.cast_mod #t #t' x) }

instance cast_tc_bool_integer (t:inttype)
  : cast_tc bool (int_t t)
  = { cast = (fun x -> if x then Rust_primitives.Integers.mk_int 1 else Rust_primitives.Integers.mk_int 0) }

/// A `char` casts as its Unicode scalar value, a `u32`, wrapping into narrower types.
instance cast_tc_char_integer (t:inttype)
  : cast_tc FStar.Char.char (int_t t)
  = { cast = (fun x ->
        Rust_primitives.Integers.cast_mod #U32 #t
          (Rust_primitives.Integers.mk_u32 (FStar.UInt32.v (FStar.Char.u32_of_char x)))) }

class unsize_tc source = {
  output: Type;
  unsize: source -> output;
}

instance array_to_slice_unsize t n: unsize_tc (t_Array t n) = {
  output = (x:t_Slice t{Seq.length x == v n});
  unsize = (fun (arr: t_Array t n) -> 
            arr <: t_Slice t);
}
