module Hax_lib

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Tactics
open Hax_lib.Prop

val v_assert (p: t_Prop) : Pure unit (requires p) (ensures (fun x -> p))
let v_assert (v__formula: t_Prop) = ()

val v_assume (p: t_Prop) : Pure unit (requires True) (ensures (fun x -> p))
let v_assume (v__formula: t_Prop) = assume v__formula


unfold let v_exists (v__f: 'a -> t_Prop): t_Prop = exists (x: 'a). v__f x
unfold let v_forall (v__f: 'a -> t_Prop): t_Prop = forall (x: 'a). v__f x
unfold let implies (lhs: t_Prop) (rhs: (x:unit{lhs} -> t_Prop)): t_Prop = (~ lhs) \/ rhs ()
