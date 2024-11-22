module Core.Array
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_TryFromSliceError = | TryFromSliceError : Prims.unit -> t_TryFromSliceError

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (Core.Primitive.t_Array v_T v_N) =
  {
    f_clone_pre = (fun (self: Core.Primitive.t_Array v_T v_N) -> true);
    f_clone_post
    =
    (fun (self: Core.Primitive.t_Array v_T v_N) (out: Core.Primitive.t_Array v_T v_N) -> true);
    f_clone
    =
    fun (self: Core.Primitive.t_Array v_T v_N) ->
      {
        Core.Primitive.f_v
        =
        Core.Clone.f_clone #(Core.Primitive.t_Slice v_T)
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive.f_v
      }
      <:
      Core.Primitive.t_Array v_T v_N
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T #v_I: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Core.Ops.Index.t_Index (Core.Primitive.t_Slice v_T) v_I)
    : Core.Ops.Index.t_Index (Core.Primitive.t_Array v_T v_N) v_I =
  {
    f_Output = i3.f_Output;
    f_index_pre = (fun (self: Core.Primitive.t_Array v_T v_N) (index: v_I) -> true);
    f_index_post
    =
    (fun (self: Core.Primitive.t_Array v_T v_N) (index: v_I) (out: i3.f_Output) -> true);
    f_index
    =
    fun (self: Core.Primitive.t_Array v_T v_N) (index: v_I) ->
      (Core.Primitive.impl_3__cast #v_T v_N self <: Core.Primitive.t_Slice v_T).[ index ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_AsRef (Core.Primitive.t_Array v_T v_N) (Core.Primitive.t_Slice v_T) =
  {
    f_as_ref_pre = (fun (self: Core.Primitive.t_Array v_T v_N) -> true);
    f_as_ref_post
    =
    (fun (self: Core.Primitive.t_Array v_T v_N) (out: Core.Primitive.t_Slice v_T) -> true);
    f_as_ref
    =
    fun (self: Core.Primitive.t_Array v_T v_N) ->
      self.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ]
  }
