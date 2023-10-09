module Rust_primitives.Arrays

open Rust_primitives.Integers

let of_list (#t:Type) l = Seq.of_list l
let to_list (#t:Type) s = Seq.seq_to_list s

let to_of_list_lemma t l = Seq.lemma_list_seq_bij l
let of_to_list_lemma t l = Seq.lemma_seq_list_bij l

let never_to_any x = admit()


