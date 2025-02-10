module Alloc.Collections.Vec_deque
open Rust_primitives

type t_VecDeque: Type0 -> unit -> Type0

val impl_5__push_back #t #a (v: t_VecDeque t a) (x: t): t_VecDeque t a

val impl_5__len #t #a (v: t_VecDeque t a): usize

val impl_5__pop_front #t #a (v: t_VecDeque t a): t_VecDeque t a & Core.Option.t_Option t


[@FStar.Tactics.Typeclasses.tcinstance]
val from_vec_deque_array t a n: Core.Convert.t_From (Alloc.Collections.Vec_deque.t_VecDeque t a)
        (Rust_primitives.Arrays.t_Array t
            (Rust_primitives.Integers.mk_usize n))

[@FStar.Tactics.Typeclasses.tcinstance]
val index_vec_deque t a: Core.Ops.Index.t_Index (Alloc.Collections.Vec_deque.t_VecDeque t a)
        Rust_primitives.Integers.usize

[@FStar.Tactics.Typeclasses.tcinstance]
val update_at t a: Rust_primitives.Hax.update_at_tc (Alloc.Collections.Vec_deque.t_VecDeque t a)
        Rust_primitives.Integers.usize
