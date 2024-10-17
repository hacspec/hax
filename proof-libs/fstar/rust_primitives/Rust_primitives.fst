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

let (let!)
    #break #continue #continue'
    (v: Core.Ops.Control_flow.t_ControlFlow break continue)
    (f: continue -> Core.Ops.Control_flow.t_ControlFlow break continue')
    : Core.Ops.Control_flow.t_ControlFlow break continue'
    = match v with
    | Core.Ops.Control_flow.ControlFlow_Continue v -> f v
    | Core.Ops.Control_flow.ControlFlow_Break b -> Core.Ops.Control_flow.ControlFlow_Break b

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
  output = (x:t_Slice t{Seq.length x == v n});
  unsize = (fun (arr: t_Array t n) -> 
            arr <: t_Slice t);
}

let rec f_while_loop #s (condition: s -> bool) (init: s) (f: (i:s -> o:s{o << i})): s
  = if condition init
    then f_while_loop #s  condition (f init) f
    else init
