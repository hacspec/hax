module Rust_primitives.Hax

open Rust_primitives.Integers
open Rust_primitives.Arrays

type t_Never = False
let never_to_any #t: t_Never -> t = (fun _ -> match () with)

let repeat (x: 'a) (len: usize): array 'a len = 
  FStar.Seq.create (v len) x
