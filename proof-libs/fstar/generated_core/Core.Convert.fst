module Core.Convert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_From (v_Self: Type0) (v_T: Type0) = {
  f_from_pre:v_T -> Type0;
  f_from_post:v_T -> v_Self -> Type0;
  f_from:x0: v_T -> Prims.Pure v_Self (f_from_pre x0) (fun result -> f_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : t_From v_T v_T =
  {
    f_from_pre = (fun (t: v_T) -> true);
    f_from_post = (fun (t: v_T) (out: v_T) -> true);
    f_from = fun (t: v_T) -> t
  }

class t_Into (v_Self: Type0) (v_T: Type0) = {
  f_into_pre:v_Self -> Type0;
  f_into_post:v_Self -> v_T -> Type0;
  f_into:x0: v_Self -> Prims.Pure v_T (f_into_pre x0) (fun result -> f_into_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T #v_U: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_From v_U v_T)
    : t_Into v_T v_U =
  {
    f_into_pre = (fun (self: v_T) -> true);
    f_into_post = (fun (self: v_T) (out: v_U) -> true);
    f_into = fun (self: v_T) -> f_from #v_U #v_T #FStar.Tactics.Typeclasses.solve self
  }
