module Hax_lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Tactics

val v_assert (p: bool) : Pure unit (requires p) (ensures (fun x -> p))
let v_assert (v__formula: bool) = ()

val v_assume (p: bool) : Pure unit (requires True) (ensures (fun x -> p))
let v_assume (v__formula: bool) = assume v__formula
