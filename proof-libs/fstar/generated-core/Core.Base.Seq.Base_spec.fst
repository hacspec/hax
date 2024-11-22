module Core.Base.Seq.Base_spec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl__clone
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
    : Core.Base.Seq.t_Seq v_T = self

let impl_1__NIL (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
    : Core.Base.Seq.t_Seq v_T = []

let impl_1__cons
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
      (t: v_T)
    : Core.Base.Seq.t_Seq v_T = t :: self

let impl_1__match_list
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
    : Core.Base.Seq.t_LIST v_T =
    match self with
    | [] -> Core.Base.Seq.LIST_NIL
    | (x :: xs) -> Core.Base.Seq.LIST_CONS x xs
