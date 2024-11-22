module Core.Array
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Core.Primitive
open Core.Cmp
open Core.Base.Int.Number_conversion

type t_Array (v_T: eqtype) (v_N: usize) = { f_v:Core.Base.Seq.t_Seq v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: eqtype)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Array v_T v_N) =
  {
    f_clone_pre = (fun (self: t_Array v_T v_N) -> true);
    f_clone_post = (fun (self: t_Array v_T v_N) (out: t_Array v_T v_N) -> true);
    f_clone
    =
    fun (self: t_Array v_T v_N) ->
      { f_v = Core.Base.Seq.Base_spec.impl__clone #v_T self.f_v } <: t_Array v_T v_N
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T: eqtype)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Cmp.t_PartialEq v_T v_T)
    : Core.Cmp.t_PartialEq (t_Array v_T v_N) (t_Array v_T v_N) =
  {
    f_eq_pre = (fun (self: t_Array v_T v_N) (other: t_Array v_T v_N) -> true);
    f_eq_post = (fun (self: t_Array v_T v_N) (other: t_Array v_T v_N) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_Array v_T v_N) (other: t_Array v_T v_N) ->
        (Core.Base.Seq.Base_spec.impl__clone #v_T self.f_v <: Core.Base.Seq.t_Seq v_T) =. other.f_v);
    f_ne_pre = (fun (self: t_Array v_T v_N) (other: t_Array v_T v_N) -> true);
    f_ne_post = (fun (self: t_Array v_T v_N) (other: t_Array v_T v_N) (out: bool) -> true);
    f_ne
    =
    fun (self: t_Array v_T v_N) (other: t_Array v_T v_N) ->
      ~.((Core.Base.Seq.Base_spec.impl__clone #v_T self.f_v <: Core.Base.Seq.t_Seq v_T) =. other.f_v
        <:
        bool)
  }

let impl_2__reverse
      (#v_T: eqtype)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: t_Array v_T v_N)
    : t_Array v_T v_N =
  { f_v = Core.Base.Seq.Base_impl.impl_2__rev #v_T self.f_v } <: t_Array v_T v_N

// let lt_usize_implies_hax_int (x y: usize)
//     : Lemma (requires x <. y)
//       (ensures
//         (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve x
//           <:
//           Core.Base.Int.t_HaxInt) <.
//         (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve y
//           <:
//           Core.Base.Int.t_HaxInt)) = admit ()

// let lift_usize_equality (x: Core.Base.Int.t_HaxInt) (y: usize)
//     : Lemma
//       (requires
//         x =.
//         (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve y
//           <:
//           Core.Base.Int.t_HaxInt))
//       (ensures
//         (Core.Convert.f_from #usize
//               #Core.Base.Int.t_HaxInt
//               #FStar.Tactics.Typeclasses.solve
//               x
//             <:
//             usize) =.
//           y) = admit ()

let impl_2__index
      (#v_T: eqtype)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: t_Array v_T v_N)
      (i: usize)
    : Prims.Pure v_T
      (requires
        // (Core.Base.Seq.Base_impl.impl_2__len #v_T self.f_v <: Core.Base.Int.t_HaxInt) =.
        // (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve v_N
        //   <:
        //   Core.Base.Int.t_HaxInt) &&
        // i <. v_N &&
    ((Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve i) <. (Core.Base.Seq.Base_impl.impl_2__len #v_T self.f_v <: Core.Base.Int.t_HaxInt)))
      (fun _ -> Prims.l_True) =
  Core.Base.Seq.Base_impl.impl_2__get_index #v_T
    self.f_v
    (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve i
      <:
      Core.Base.Int.t_HaxInt)

let impl_2__new
      (#v_T: eqtype)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (x: v_T)
    : t_Array v_T v_N =
  {
    f_v
    =
    Core.Base.Seq.Base_impl.impl_2__repeat #v_T
      (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve v_N
        <:
        Core.Base.Int.t_HaxInt)
      x
  }
  <:
  t_Array v_T v_N

let impl_2__set_index
      (#v_T: eqtype)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: t_Array v_T v_N)
      (i: usize)
      (t: v_T)
    : Prims.Pure (t_Array v_T v_N)
      (requires
        // (Core.Base.Seq.Base_impl.impl_2__len #v_T self.f_v <: Core.Base.Int.t_HaxInt) =.
        // (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve v_N
        //   <:
        //   Core.Base.Int.t_HaxInt) &&
        // i <. v_N &&
    ((Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve i) <. (Core.Base.Seq.Base_impl.impl_2__len #v_T self.f_v <: Core.Base.Int.t_HaxInt)))
      (fun _ -> Prims.l_True) =
  {
    f_v
    =
    Core.Base.Seq.Base_impl.impl_2__set_index #v_T
      self.f_v
      (Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve i
        <:
        Core.Base.Int.t_HaxInt)
      t
  }
  <:
  t_Array v_T v_N
