module Core.Slice.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Iter (v_T: Type0) = {
  f_data:Core.Primitive.t_Slice v_T;
  f__marker:Core.Marker.t_PhantomData v_T
}

let impl__new
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (slice: Core.Primitive.t_Slice v_T)
    : t_Iter v_T =
  {
    f_data = Core.Clone.f_clone #(Core.Primitive.t_Slice v_T) #FStar.Tactics.Typeclasses.solve slice;
    f__marker = Core.Marker.PhantomData <: Core.Marker.t_PhantomData v_T
  }
  <:
  t_Iter v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Iter v_T) =
  {
    f_clone_pre = (fun (self: t_Iter v_T) -> true);
    f_clone_post = (fun (self: t_Iter v_T) (out: t_Iter v_T) -> true);
    f_clone
    =
    fun (self: t_Iter v_T) ->
      {
        f_data
        =
        Core.Clone.f_clone #(Core.Primitive.t_Slice v_T)
          #FStar.Tactics.Typeclasses.solve
          self.f_data;
        f__marker = self.f__marker
      }
      <:
      t_Iter v_T
  }
