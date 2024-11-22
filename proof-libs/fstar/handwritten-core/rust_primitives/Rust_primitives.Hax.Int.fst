module Rust_primitives.Hax.Int

open Core
open Rust_primitives
module LI = Lib.IntTypes

unfold let from_machine (#t:inttype) (x:int_t t) : range_t t = v #t x
unfold let into_machine (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
