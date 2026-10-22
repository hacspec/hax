module New_tests.Rustc_coverage__simple_loop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

/// @fail(extraction): fstar(HAX0001), coq(HAX0001, HAX0001), legacy-lean(HAX0001), proverif(HAX0008), ssprove(HAX0001)
let main (_: Prims.unit) : (i32 & Prims.unit) =
  let is_true:bool =
    (Core_models.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) =.
    mk_usize 1
  in
  let countdown:i32 = mk_i32 0 in
  let countdown:i32 =
    if is_true
    then
      let countdown:i32 = mk_i32 10 in
      countdown
    else countdown
  in
  Rust_primitives.Hax.failure "[hax::opaque] something is not implemented yet. Unhandled loop kind"
    "",
  ()
  <:
  (i32 & Prims.unit)
