module Hacspec_chacha20.A_module
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

let h: Prims.unit = ()