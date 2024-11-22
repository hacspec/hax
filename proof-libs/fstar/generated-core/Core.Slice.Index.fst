module Core.Slice.Index
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_SliceIndex (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9346575357466912174:Core.Slice.Index.Private_slice_index.t_Sealed
  v_Self;
  f_Output:Type0;
  f_index_pre:v_Self -> v_T -> Type0;
  f_index_post:v_Self -> v_T -> f_Output -> Type0;
  f_index:x0: v_Self -> x1: v_T
    -> Prims.Pure f_Output (f_index_pre x0 x1) (fun result -> f_index_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_SliceIndex v_I (Core.Primitive.t_Slice v_T))
    : Core.Ops.Index.t_Index (Core.Primitive.t_Slice v_T) v_I =
  {
    f_Output = i2.f_Output;
    f_index_pre = (fun (self: Core.Primitive.t_Slice v_T) (index: v_I) -> true);
    f_index_post = (fun (self: Core.Primitive.t_Slice v_T) (index: v_I) (out: i2.f_Output) -> true);
    f_index
    =
    fun (self: Core.Primitive.t_Slice v_T) (index: v_I) ->
      f_index #v_I #(Core.Primitive.t_Slice v_T) #FStar.Tactics.Typeclasses.solve index self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : t_SliceIndex Core.Ops.Range.t_RangeFull (Core.Primitive.t_Slice v_T) =
  {
    _super_9346575357466912174 = FStar.Tactics.Typeclasses.solve;
    f_Output = Core.Primitive.t_Slice v_T;
    f_index_pre
    =
    (fun (self: Core.Ops.Range.t_RangeFull) (slice: Core.Primitive.t_Slice v_T) -> true);
    f_index_post
    =
    (fun
        (self: Core.Ops.Range.t_RangeFull)
        (slice: Core.Primitive.t_Slice v_T)
        (out: Core.Primitive.t_Slice v_T)
        ->
        true);
    f_index = fun (self: Core.Ops.Range.t_RangeFull) (slice: Core.Primitive.t_Slice v_T) -> slice
  }

/// The methods `index` and `index_mut` panic if the index is out of bounds.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : t_SliceIndex Core.Primitive.t_usize (Core.Primitive.t_Slice v_T) =
  {
    _super_9346575357466912174 = FStar.Tactics.Typeclasses.solve;
    f_Output = v_T;
    f_index_pre = (fun (self: Core.Primitive.t_usize) (slice: Core.Primitive.t_Slice v_T) -> true);
    f_index_post
    =
    (fun (self: Core.Primitive.t_usize) (slice: Core.Primitive.t_Slice v_T) (out: v_T) -> true);
    f_index
    =
    fun (self: Core.Primitive.t_usize) (slice: Core.Primitive.t_Slice v_T) ->
      let (x: usize):usize =
        Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
          #usize
          #FStar.Tactics.Typeclasses.solve
          self.Core.Primitive._0.Core.Base_interface.Int.f_v
      in
      slice.Core.Primitive.f_v.Core.Base.Spec.Seq.f_v.[ x ]
  }
