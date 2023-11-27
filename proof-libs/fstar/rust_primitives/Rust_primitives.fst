module Rust_primitives

include Rust_primitives.Integers
include Rust_primitives.Arrays

inline_for_extraction
class cast_tc a b = {
  cast: a -> b; 
}

/// Rust's casts operations on integers are non-panicking
inline_for_extraction
instance cast_tc_integers (t:inttype) (t':inttype)
  : cast_tc (int_t t) (int_t t')
  = { cast = (fun x -> Rust_primitives.Integers.cast_mod #t #t' x) }

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

inline_for_extraction
class unsize_tc source = {
  output: Type;
  unsize: source -> output
}

inline_for_extraction
instance array_to_slice_unsize t n: unsize_tc (t_Array t n) = {
  output = t_Slice t;
  unsize = (fun (arr: t_Array t n) -> 
    {buffer = arr; len = n}
  );
}

open FStar.HyperStack
open FStar.HyperStack.ST

// open Lib.IntTypes

inline_for_extraction
val f_for_loop: #n: inttype ->
    start: int_t n
  -> finish: int_t n {v finish >= v start}
  -> f:(i:int_t n (*{v start <= v i /\ v i < v finish}*) -> St unit) ->
  St unit
let f_for_loop #n start0 finish0 f = 
    let start  = Rust_primitives.Integers.cast_mod start0  in
    let finish = Rust_primitives.Integers.cast_mod finish0 in
    admitP (v finish0 >= v start0 ==> v finish >= v start);
    Lib.Loops.for
        start finish
        (fun _ _ -> True)
        (fun i -> f (Rust_primitives.Integers.cast_mod i); admit ())

