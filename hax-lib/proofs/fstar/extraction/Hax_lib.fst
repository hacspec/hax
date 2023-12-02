module Hax_lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Tactics

val v_assert (p: bool) : Pure unit (requires p) (ensures (fun x -> p))
let v_assert (v__formula: bool) = ()

val v_assume (p: bool) : Pure unit (requires True) (ensures (fun x -> p))
let v_assume (v__formula: bool) = assume v__formula


unfold let v_exists (v__f: 'a -> Type0): Type0 = exists (x: 'a). v__f x
unfold let v_forall (v__f: 'a -> Type0): Type0 = forall (x: 'a). v__f x
unfold let implies (lhs: bool) (rhs: (x:unit{lhs} -> bool)): bool = if lhs then rhs() else true
