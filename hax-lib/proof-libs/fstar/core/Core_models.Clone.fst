module Core_models.Clone
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_Clone self = {
  f_clone_pre: self -> Type0;
  f_clone_post: self -> self -> Type0;
  f_clone: x:self -> r:self {x == r}
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let clone_identity (#v_T: Type0) : t_Clone v_T =
  {
    f_clone_pre = (fun (self: v_T) -> true);
    f_clone_post = (fun (self: v_T) (out: v_T) -> true);
    f_clone = fun (self: v_T) -> self
  }

/// See [`std::clone::TrivialClone`]
class t_TrivialClone (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Clone v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_TrivialClone v_Self|} -> i._super_i0

/// See [`std::clone::UseCloned`]
class t_UseCloned (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Clone v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_UseCloned v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Clone v_T)
    : t_TrivialClone v_T = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Clone v_T)
    : t_UseCloned v_T = { _super_i0 = FStar.Tactics.Typeclasses.solve }
