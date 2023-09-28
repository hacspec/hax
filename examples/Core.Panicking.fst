module Core.Panicking

open Core.Types
open Rust_primitives.Hax

type t_AssertKind = | AssertKind_Eq

let panic (message: string {False}): t_Never
  = match () with
  
let assert_failed (k: t_AssertKind) x y (z: _ {False}): t_Never
  = match () with
