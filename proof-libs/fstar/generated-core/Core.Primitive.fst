module Core.Primitive
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Slice (v_T: Type0) = { f_v:Core.Base.Spec.Seq.t_Seq v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_From (t_Slice v_T) (t_Slice v_T) =
  {
    f_from_pre = (fun (x: t_Slice v_T) -> true);
    f_from_post = (fun (x: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_from
    =
    fun (x: t_Slice v_T) ->
      {
        f_v
        =
        { Core.Base.Spec.Seq.f_v = Alloc.Slice.impl__to_vec #v_T x } <: Core.Base.Spec.Seq.t_Seq v_T
      }
      <:
      t_Slice v_T
  }

type t_Array (v_T: Type0) (v_N: usize) = { f_v:t_Slice v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_From (t_Array v_T v_N) (t_Array v_T v_N) =
  {
    f_from_pre = (fun (x: t_Array v_T v_N) -> true);
    f_from_post = (fun (x: t_Array v_T v_N) (out: t_Array v_T v_N) -> true);
    f_from
    =
    fun (x: t_Array v_T v_N) ->
      {
        f_v
        =
        {
          f_v
          =
          {
            Core.Base.Spec.Seq.f_v
            =
            Alloc.Slice.impl__to_vec #v_T
              (x.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ] <: t_Slice v_T)
          }
          <:
          Core.Base.Spec.Seq.t_Seq v_T
        }
        <:
        t_Slice v_T
      }
      <:
      t_Array v_T v_N
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_From (t_Array v_T v_N) (t_Array v_T v_N) =
  {
    f_from_pre = (fun (x: t_Array v_T v_N) -> true);
    f_from_post = (fun (x: t_Array v_T v_N) (out: t_Array v_T v_N) -> true);
    f_from
    =
    fun (x: t_Array v_T v_N) ->
      match
        Core.Convert.f_try_into #(Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global)
          #(t_Array v_T v_N)
          #FStar.Tactics.Typeclasses.solve
          x.f_v.f_v.Core.Base.Spec.Seq.f_v
      with
      | Core.Result.Result_Ok x -> x
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_const (sz 1
                  )
                  (let list = ["some error?"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
  }

let impl_3__cast
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (self: t_Array v_T v_N)
    : t_Slice v_T = self.f_v

type t_u128 = | C_u128 : Core.Base_interface.Int.t_U128 -> t_u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Clone.t_Clone t_u128 =
  {
    f_clone_pre = (fun (self: t_u128) -> true);
    f_clone_post = (fun (self: t_u128) (out: t_u128) -> true);
    f_clone
    =
    fun (self: t_u128) ->
      C_u128
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U128 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Cmp.t_PartialEq t_u128 t_u128 =
  {
    f_eq_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_eq_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_eq = (fun (self: t_u128) (rhs: t_u128) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_ne_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_ne = fun (self: t_u128) (rhs: t_u128) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Cmp.t_PartialOrd t_u128 t_u128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u128) (rhs: t_u128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_lt_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
            #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_le_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
            #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_gt_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
            #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_ge_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u128) (rhs: t_u128) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u16 = | C_u16 : Core.Base_interface.Int.t_U16 -> t_u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Clone.t_Clone t_u16 =
  {
    f_clone_pre = (fun (self: t_u16) -> true);
    f_clone_post = (fun (self: t_u16) (out: t_u16) -> true);
    f_clone
    =
    fun (self: t_u16) ->
      C_u16
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U16 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Cmp.t_PartialEq t_u16 t_u16 =
  {
    f_eq_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_eq_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_eq = (fun (self: t_u16) (rhs: t_u16) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_ne_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_ne = fun (self: t_u16) (rhs: t_u16) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Cmp.t_PartialOrd t_u16 t_u16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u16) (rhs: t_u16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_lt_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
            #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_le_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
            #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_gt_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
            #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_ge_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u16) (rhs: t_u16) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u32 = | C_u32 : Core.Base_interface.Int.t_U32 -> t_u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Clone.t_Clone t_u32 =
  {
    f_clone_pre = (fun (self: t_u32) -> true);
    f_clone_post = (fun (self: t_u32) (out: t_u32) -> true);
    f_clone
    =
    fun (self: t_u32) ->
      C_u32
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U32 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Cmp.t_PartialEq t_u32 t_u32 =
  {
    f_eq_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_eq_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_eq = (fun (self: t_u32) (rhs: t_u32) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_ne_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_ne = fun (self: t_u32) (rhs: t_u32) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Cmp.t_PartialOrd t_u32 t_u32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u32) (rhs: t_u32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_lt_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
            #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_le_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
            #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_gt_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
            #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_ge_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u32) (rhs: t_u32) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u64 = | C_u64 : Core.Base_interface.Int.t_U64 -> t_u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Clone.t_Clone t_u64 =
  {
    f_clone_pre = (fun (self: t_u64) -> true);
    f_clone_post = (fun (self: t_u64) (out: t_u64) -> true);
    f_clone
    =
    fun (self: t_u64) ->
      C_u64
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Cmp.t_PartialEq t_u64 t_u64 =
  {
    f_eq_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_eq_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_eq = (fun (self: t_u64) (rhs: t_u64) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_ne_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_ne = fun (self: t_u64) (rhs: t_u64) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Cmp.t_PartialOrd t_u64 t_u64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u64) (rhs: t_u64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_lt_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_le_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_gt_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_ge_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u64) (rhs: t_u64) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u8 = | C_u8 : Core.Base_interface.Int.t_U8 -> t_u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Clone.t_Clone t_u8 =
  {
    f_clone_pre = (fun (self: t_u8) -> true);
    f_clone_post = (fun (self: t_u8) (out: t_u8) -> true);
    f_clone
    =
    fun (self: t_u8) ->
      C_u8
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U8 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Cmp.t_PartialEq t_u8 t_u8 =
  {
    f_eq_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_eq_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_eq = (fun (self: t_u8) (rhs: t_u8) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_ne_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_ne = fun (self: t_u8) (rhs: t_u8) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Cmp.t_PartialOrd t_u8 t_u8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u8) (rhs: t_u8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_lt_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
            #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_le_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
            #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_gt_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
            #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_ge_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u8) (rhs: t_u8) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_usize = | C_usize : Core.Base_interface.Int.t_U64 -> t_usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Clone.t_Clone t_usize =
  {
    f_clone_pre = (fun (self: t_usize) -> true);
    f_clone_post = (fun (self: t_usize) (out: t_usize) -> true);
    f_clone
    =
    fun (self: t_usize) ->
      C_usize
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Cmp.t_PartialEq t_usize t_usize =
  {
    f_eq_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_eq_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_eq = (fun (self: t_usize) (rhs: t_usize) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_ne_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_ne = fun (self: t_usize) (rhs: t_usize) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Cmp.t_PartialOrd t_usize t_usize =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_usize) (rhs: t_usize) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_lt_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_le_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_le
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_gt_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_ge_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_ge
    =
    fun (self: t_usize) (rhs: t_usize) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_i128 = | C_i128 : Core.Base_interface.Int.t_I128 -> t_i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Clone.t_Clone t_i128 =
  {
    f_clone_pre = (fun (self: t_i128) -> true);
    f_clone_post = (fun (self: t_i128) (out: t_i128) -> true);
    f_clone
    =
    fun (self: t_i128) ->
      C_i128
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I128 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Cmp.t_PartialEq t_i128 t_i128 =
  {
    f_eq_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_eq_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_eq = (fun (self: t_i128) (rhs: t_i128) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_ne_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_ne = fun (self: t_i128) (rhs: t_i128) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Cmp.t_PartialOrd t_i128 t_i128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i128) (rhs: t_i128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_lt_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
            #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_le_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
            #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_gt_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
            #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_ge_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i128) (rhs: t_i128) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_i16 = | C_i16 : Core.Base_interface.Int.t_I16 -> t_i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Clone.t_Clone t_i16 =
  {
    f_clone_pre = (fun (self: t_i16) -> true);
    f_clone_post = (fun (self: t_i16) (out: t_i16) -> true);
    f_clone
    =
    fun (self: t_i16) ->
      C_i16
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I16 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Cmp.t_PartialEq t_i16 t_i16 =
  {
    f_eq_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_eq_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_eq = (fun (self: t_i16) (rhs: t_i16) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_ne_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_ne = fun (self: t_i16) (rhs: t_i16) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Cmp.t_PartialOrd t_i16 t_i16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i16) (rhs: t_i16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_lt_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
            #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_le_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
            #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_gt_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
            #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_ge_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i16) (rhs: t_i16) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_i32 = | C_i32 : Core.Base_interface.Int.t_I32 -> t_i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Clone.t_Clone t_i32 =
  {
    f_clone_pre = (fun (self: t_i32) -> true);
    f_clone_post = (fun (self: t_i32) (out: t_i32) -> true);
    f_clone
    =
    fun (self: t_i32) ->
      C_i32
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I32 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Cmp.t_PartialEq t_i32 t_i32 =
  {
    f_eq_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_eq_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_eq = (fun (self: t_i32) (rhs: t_i32) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_ne_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_ne = fun (self: t_i32) (rhs: t_i32) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Cmp.t_PartialOrd t_i32 t_i32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i32) (rhs: t_i32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_lt_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
            #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_le_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
            #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_gt_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
            #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_ge_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i32) (rhs: t_i32) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_i64 = | C_i64 : Core.Base_interface.Int.t_I64 -> t_i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Clone.t_Clone t_i64 =
  {
    f_clone_pre = (fun (self: t_i64) -> true);
    f_clone_post = (fun (self: t_i64) (out: t_i64) -> true);
    f_clone
    =
    fun (self: t_i64) ->
      C_i64
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: Core.Cmp.t_PartialEq t_i64 t_i64 =
  {
    f_eq_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_eq_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_eq = (fun (self: t_i64) (rhs: t_i64) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_ne_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_ne = fun (self: t_i64) (rhs: t_i64) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: Core.Cmp.t_PartialOrd t_i64 t_i64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i64) (rhs: t_i64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_lt_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_le_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_gt_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_ge_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i64) (rhs: t_i64) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_i8 = | C_i8 : Core.Base_interface.Int.t_I8 -> t_i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Clone.t_Clone t_i8 =
  {
    f_clone_pre = (fun (self: t_i8) -> true);
    f_clone_post = (fun (self: t_i8) (out: t_i8) -> true);
    f_clone
    =
    fun (self: t_i8) ->
      C_i8
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I8 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Cmp.t_PartialEq t_i8 t_i8 =
  {
    f_eq_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_eq_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_eq = (fun (self: t_i8) (rhs: t_i8) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_ne_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_ne = fun (self: t_i8) (rhs: t_i8) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Cmp.t_PartialOrd t_i8 t_i8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i8) (rhs: t_i8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_lt_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
            #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_le_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
            #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_gt_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
            #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_ge_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i8) (rhs: t_i8) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_isize = | C_isize : Core.Base_interface.Int.t_I64 -> t_isize

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Clone.t_Clone t_isize =
  {
    f_clone_pre = (fun (self: t_isize) -> true);
    f_clone_post = (fun (self: t_isize) (out: t_isize) -> true);
    f_clone
    =
    fun (self: t_isize) ->
      C_isize
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Cmp.t_PartialEq t_isize t_isize =
  {
    f_eq_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_eq_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_eq = (fun (self: t_isize) (rhs: t_isize) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_ne_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_ne = fun (self: t_isize) (rhs: t_isize) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Cmp.t_PartialOrd t_isize t_isize =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_isize) (rhs: t_isize) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_lt_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_le_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_le
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_gt_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_ge_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_ge
    =
    fun (self: t_isize) (rhs: t_isize) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }
