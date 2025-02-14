module Hax_lib.Prop
open Rust_primitives
type t_Prop = Type0

val v_assert (p: t_Prop) : Pure unit (requires p) (ensures (fun x -> p))
let v_assert (v__formula: t_Prop) = ()

val v_assume (p: t_Prop) : Pure unit (requires True) (ensures (fun x -> p))
let v_assume (v__formula: t_Prop) = assume v__formula


unfold let v_exists (#t:Type0) (#p:Type) (v__f: usize -> t_Prop): t_Prop = exists (x: usize). v__f x
unfold let v_forall (#t:Type0) (#p:Type) (v__f: usize -> t_Prop): t_Prop = forall (x: usize). v__f x
unfold let implies (#t1:Type) (#t2:Type) (lhs: t_Prop) (rhs: (x:unit{lhs} -> t_Prop)): t_Prop = (~ lhs) \/ rhs ()
