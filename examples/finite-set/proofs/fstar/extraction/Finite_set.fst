module Finite_set
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let insert_assert_len: Prims.unit =
  let (s: Std.Collections.Hash.Set.t_HashSet i32 Std.Collections.Hash.Map.t_RandomState):Std.Collections.Hash.Set.t_HashSet
    i32 Std.Collections.Hash.Map.t_RandomState =
    Std.Collections.Hash.Set.impl__new
  in
  let _:Prims.unit =
    if ~.((Std.Collections.Hash.Set.impl_1__len s <: usize) =. sz 0 <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: s.len() == 0"
          <:
          Rust_primitives.Hax.t_Never)
  in
  ()

let main: Prims.unit =
  let _:Prims.unit = insert_assert_len in
  ()
