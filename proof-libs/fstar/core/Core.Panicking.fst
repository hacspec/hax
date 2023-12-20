module Core.Panicking

open Rust_primitives
open Rust_primitives.Hax

type t_AssertKind = | AssertKind_Eq

let panic (message: string {False}): t_Never
  = match () with
  
let assert_failed (k: t_AssertKind) x y (z: Core.Option.t_Option unit {False}): t_Never
  = match () with
