module Core.Base.Spec.Seq
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Seq (v_T: Type0) = { f_v:Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Seq v_T) =
  {
    f_clone_pre = (fun (self: t_Seq v_T) -> true);
    f_clone_post = (fun (self: t_Seq v_T) (out: t_Seq v_T) -> true);
    f_clone
    =
    fun (self: t_Seq v_T) ->
      {
        f_v
        =
        Core.Clone.f_clone #(Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          self.f_v
      }
      <:
      t_Seq v_T
  }

type t_LIST (v_T: Type0) =
  | LIST_NIL : t_LIST v_T
  | LIST_CONS : v_T -> t_Seq v_T -> t_LIST v_T

let nil
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (_: Prims.unit)
    : t_Seq v_T = { f_v = Alloc.Vec.impl__new #v_T () } <: t_Seq v_T

let cons
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: t_Seq v_T)
      (t: v_T)
    : t_Seq v_T =
  {
    f_v
    =
    Alloc.Slice.impl__concat #(t_Slice v_T)
      #v_T
      ((let list =
            [
              (let list = [t] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list).[ Core.Ops.Range.RangeFull
                <:
                Core.Ops.Range.t_RangeFull ];
              s.f_v.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ]
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice (t_Slice v_T))
  }
  <:
  t_Seq v_T

let match_list
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: t_Seq v_T)
    : t_LIST v_T =
  if
    Rust_primitives.Usize.eq (Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global s.f_v <: usize)
      (sz 0)
  then LIST_NIL <: t_LIST v_T
  else
    LIST_CONS (Core.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve (s.f_v.[ sz 0 ] <: v_T))
      ({
          f_v
          =
          Alloc.Slice.impl__concat #(t_Slice v_T)
            #v_T
            ((let list =
                  [s.f_v.[ { Core.Ops.Range.f_start = sz 1 } <: Core.Ops.Range.t_RangeFrom usize ]]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              <:
              t_Slice (t_Slice v_T))
        }
        <:
        t_Seq v_T)
    <:
    t_LIST v_T
