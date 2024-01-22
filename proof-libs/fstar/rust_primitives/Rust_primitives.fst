module Rust_primitives

include Rust_primitives.Integers
include Rust_primitives.Arrays
include Rust_primitives.BitVectors

let (let?) 
  (#a #b: Type)
  (x: Core.Option.t_Option a) (f: a -> Core.Option.t_Option b): Core.Option.t_Option b
  = match x with
  | Core.Option.Option_Some x -> f x
  | Core.Option.Option_None   -> Core.Option.Option_None

let (let|) (#e #a #b: Type) (x: Core.Result.t_Result a e) (f: a -> Core.Result.t_Result b e)
    : Core.Result.t_Result b e
    = match x with
    | Core.Result.Result_Ok x -> f x
    | Core.Result.Result_Err e -> Core.Result.Result_Err e

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


