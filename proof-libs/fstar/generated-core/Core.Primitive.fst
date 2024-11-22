module Core.Primitive
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Core.Cmp
open Core.Ops.Arith
open Core.Ops.Bit

type t_u128 = | C_u128 : Core.Int.t_U128 -> t_u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Clone.t_Clone t_u128 =
  {
    f_clone_pre = (fun (self: t_u128) -> true);
    f_clone_post = (fun (self: t_u128) (out: t_u128) -> true);
    f_clone
    =
    fun (self: t_u128) ->
      C_u128 (Core.Clone.f_clone #Core.Int.t_U128 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Cmp.t_PartialEq t_u128 t_u128 =
  {
    f_eq_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_eq_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_eq = (fun (self: t_u128) (rhs: t_u128) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_ne_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_ne = fun (self: t_u128) (rhs: t_u128) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Cmp.t_PartialOrd t_u128 t_u128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u128) (rhs: t_u128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        Core.Cmp.f_partial_cmp #Core.Int.t_U128
          #Core.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_lt_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Int.t_U128
            #Core.Int.t_U128
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U128
            #Core.Int.t_U128
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U128
            #Core.Int.t_U128
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
        Core.Cmp.f_partial_cmp #Core.Int.t_U128
          #Core.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u16 = | C_u16 : Core.Int.t_U16 -> t_u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Clone.t_Clone t_u16 =
  {
    f_clone_pre = (fun (self: t_u16) -> true);
    f_clone_post = (fun (self: t_u16) (out: t_u16) -> true);
    f_clone
    =
    fun (self: t_u16) ->
      C_u16 (Core.Clone.f_clone #Core.Int.t_U16 #FStar.Tactics.Typeclasses.solve self._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Cmp.t_PartialEq t_u16 t_u16 =
  {
    f_eq_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_eq_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_eq = (fun (self: t_u16) (rhs: t_u16) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_ne_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_ne = fun (self: t_u16) (rhs: t_u16) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Cmp.t_PartialOrd t_u16 t_u16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u16) (rhs: t_u16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        Core.Cmp.f_partial_cmp #Core.Int.t_U16
          #Core.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_lt_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Int.t_U16
            #Core.Int.t_U16
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U16
            #Core.Int.t_U16
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U16
            #Core.Int.t_U16
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
        Core.Cmp.f_partial_cmp #Core.Int.t_U16
          #Core.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u32 = | C_u32 : Core.Int.t_U32 -> t_u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Clone.t_Clone t_u32 =
  {
    f_clone_pre = (fun (self: t_u32) -> true);
    f_clone_post = (fun (self: t_u32) (out: t_u32) -> true);
    f_clone
    =
    fun (self: t_u32) ->
      C_u32 (Core.Clone.f_clone #Core.Int.t_U32 #FStar.Tactics.Typeclasses.solve self._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Cmp.t_PartialEq t_u32 t_u32 =
  {
    f_eq_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_eq_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_eq = (fun (self: t_u32) (rhs: t_u32) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_ne_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_ne = fun (self: t_u32) (rhs: t_u32) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Cmp.t_PartialOrd t_u32 t_u32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u32) (rhs: t_u32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        Core.Cmp.f_partial_cmp #Core.Int.t_U32
          #Core.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_lt_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Int.t_U32
            #Core.Int.t_U32
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U32
            #Core.Int.t_U32
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U32
            #Core.Int.t_U32
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
        Core.Cmp.f_partial_cmp #Core.Int.t_U32
          #Core.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u64 = | C_u64 : Core.Int.t_U64 -> t_u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Clone.t_Clone t_u64 =
  {
    f_clone_pre = (fun (self: t_u64) -> true);
    f_clone_post = (fun (self: t_u64) (out: t_u64) -> true);
    f_clone
    =
    fun (self: t_u64) ->
      C_u64 (Core.Clone.f_clone #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve self._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Cmp.t_PartialEq t_u64 t_u64 =
  {
    f_eq_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_eq_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_eq = (fun (self: t_u64) (rhs: t_u64) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_ne_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_ne = fun (self: t_u64) (rhs: t_u64) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Cmp.t_PartialOrd t_u64 t_u64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u64) (rhs: t_u64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        Core.Cmp.f_partial_cmp #Core.Int.t_U64
          #Core.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_lt_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Int.t_U64
            #Core.Int.t_U64
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U64
            #Core.Int.t_U64
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U64
            #Core.Int.t_U64
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
        Core.Cmp.f_partial_cmp #Core.Int.t_U64
          #Core.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_u8 = | C_u8 : Core.Int.t_U8 -> t_u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Clone.t_Clone t_u8 =
  {
    f_clone_pre = (fun (self: t_u8) -> true);
    f_clone_post = (fun (self: t_u8) (out: t_u8) -> true);
    f_clone
    =
    fun (self: t_u8) ->
      C_u8 (Core.Clone.f_clone #Core.Int.t_U8 #FStar.Tactics.Typeclasses.solve self._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Cmp.t_PartialEq t_u8 t_u8 =
  {
    f_eq_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_eq_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_eq = (fun (self: t_u8) (rhs: t_u8) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_ne_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_ne = fun (self: t_u8) (rhs: t_u8) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Cmp.t_PartialOrd t_u8 t_u8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u8) (rhs: t_u8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        Core.Cmp.f_partial_cmp #Core.Int.t_U8
          #Core.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_lt_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Int.t_U8
            #Core.Int.t_U8
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U8
            #Core.Int.t_U8
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U8
            #Core.Int.t_U8
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
        Core.Cmp.f_partial_cmp #Core.Int.t_U8
          #Core.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

type t_usize = | C_usize : Core.Int.t_U64 -> t_usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Clone.t_Clone t_usize =
  {
    f_clone_pre = (fun (self: t_usize) -> true);
    f_clone_post = (fun (self: t_usize) (out: t_usize) -> true);
    f_clone
    =
    fun (self: t_usize) ->
      C_usize (Core.Clone.f_clone #Core.Int.t_U64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Cmp.t_PartialEq t_usize t_usize =
  {
    f_eq_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_eq_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_eq = (fun (self: t_usize) (rhs: t_usize) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_ne_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_ne = fun (self: t_usize) (rhs: t_usize) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Cmp.t_PartialOrd t_usize t_usize =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_usize) (rhs: t_usize) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        Core.Cmp.f_partial_cmp #Core.Int.t_U64
          #Core.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_lt_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Int.t_U64
            #Core.Int.t_U64
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U64
            #Core.Int.t_U64
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
          Core.Cmp.f_partial_cmp #Core.Int.t_U64
            #Core.Int.t_U64
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
        Core.Cmp.f_partial_cmp #Core.Int.t_U64
          #Core.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Arith.t_Mul t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_mul_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_mul_post = (fun (self: t_u8) (rhs: t_u8) (out: t_u8) -> true);
    f_mul = fun (self: t_u8) (rhs: t_u8) -> C_u8 (self._0 *! rhs._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Ops.Arith.t_Rem t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_rem_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_rem_post = (fun (self: t_u8) (rhs: t_u8) (out: t_u8) -> true);
    f_rem = fun (self: t_u8) (rhs: t_u8) -> C_u8 (self._0 %! rhs._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Ops.Arith.t_Add t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_add_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_add_post = (fun (self: t_u8) (rhs: t_u8) (out: t_u8) -> true);
    f_add = fun (self: t_u8) (rhs: t_u8) -> C_u8 (self._0 +! rhs._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Ops.Arith.t_Div t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_div_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_div_post = (fun (self: t_u8) (rhs: t_u8) (out: t_u8) -> true);
    f_div = fun (self: t_u8) (rhs: t_u8) -> C_u8 (self._0 /! rhs._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Ops.Arith.t_Mul t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_mul_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_mul_post = (fun (self: t_u16) (rhs: t_u16) (out: t_u16) -> true);
    f_mul = fun (self: t_u16) (rhs: t_u16) -> C_u16 (self._0 *! rhs._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Ops.Arith.t_Rem t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_rem_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_rem_post = (fun (self: t_u16) (rhs: t_u16) (out: t_u16) -> true);
    f_rem = fun (self: t_u16) (rhs: t_u16) -> C_u16 (self._0 %! rhs._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Ops.Arith.t_Add t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_add_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_add_post = (fun (self: t_u16) (rhs: t_u16) (out: t_u16) -> true);
    f_add = fun (self: t_u16) (rhs: t_u16) -> C_u16 (self._0 +! rhs._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Ops.Arith.t_Div t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_div_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_div_post = (fun (self: t_u16) (rhs: t_u16) (out: t_u16) -> true);
    f_div = fun (self: t_u16) (rhs: t_u16) -> C_u16 (self._0 /! rhs._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Ops.Arith.t_Mul t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_mul_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_mul_post = (fun (self: t_u32) (rhs: t_u32) (out: t_u32) -> true);
    f_mul = fun (self: t_u32) (rhs: t_u32) -> C_u32 (self._0 *! rhs._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Ops.Arith.t_Rem t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_rem_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_rem_post = (fun (self: t_u32) (rhs: t_u32) (out: t_u32) -> true);
    f_rem = fun (self: t_u32) (rhs: t_u32) -> C_u32 (self._0 %! rhs._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Ops.Arith.t_Add t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_add_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_add_post = (fun (self: t_u32) (rhs: t_u32) (out: t_u32) -> true);
    f_add = fun (self: t_u32) (rhs: t_u32) -> C_u32 (self._0 +! rhs._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Ops.Arith.t_Div t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_div_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_div_post = (fun (self: t_u32) (rhs: t_u32) (out: t_u32) -> true);
    f_div = fun (self: t_u32) (rhs: t_u32) -> C_u32 (self._0 /! rhs._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Ops.Arith.t_Mul t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_mul_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_mul_post = (fun (self: t_u64) (rhs: t_u64) (out: t_u64) -> true);
    f_mul = fun (self: t_u64) (rhs: t_u64) -> C_u64 (self._0 *! rhs._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Ops.Arith.t_Rem t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_rem_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_rem_post = (fun (self: t_u64) (rhs: t_u64) (out: t_u64) -> true);
    f_rem = fun (self: t_u64) (rhs: t_u64) -> C_u64 (self._0 %! rhs._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Ops.Arith.t_Add t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_add_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_add_post = (fun (self: t_u64) (rhs: t_u64) (out: t_u64) -> true);
    f_add = fun (self: t_u64) (rhs: t_u64) -> C_u64 (self._0 +! rhs._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Ops.Arith.t_Div t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_div_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_div_post = (fun (self: t_u64) (rhs: t_u64) (out: t_u64) -> true);
    f_div = fun (self: t_u64) (rhs: t_u64) -> C_u64 (self._0 /! rhs._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Ops.Arith.t_Mul t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_mul_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_mul_post = (fun (self: t_u128) (rhs: t_u128) (out: t_u128) -> true);
    f_mul = fun (self: t_u128) (rhs: t_u128) -> C_u128 (self._0 *! rhs._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Ops.Arith.t_Rem t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_rem_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_rem_post = (fun (self: t_u128) (rhs: t_u128) (out: t_u128) -> true);
    f_rem = fun (self: t_u128) (rhs: t_u128) -> C_u128 (self._0 %! rhs._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Ops.Arith.t_Add t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_add_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_add_post = (fun (self: t_u128) (rhs: t_u128) (out: t_u128) -> true);
    f_add = fun (self: t_u128) (rhs: t_u128) -> C_u128 (self._0 +! rhs._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Ops.Arith.t_Div t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_div_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_div_post = (fun (self: t_u128) (rhs: t_u128) (out: t_u128) -> true);
    f_div = fun (self: t_u128) (rhs: t_u128) -> C_u128 (self._0 /! rhs._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Ops.Arith.t_Mul t_usize t_usize =
  {
    f_Output = t_usize;
    f_mul_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_mul_post = (fun (self: t_usize) (rhs: t_usize) (out: t_usize) -> true);
    f_mul = fun (self: t_usize) (rhs: t_usize) -> C_usize (self._0 *! rhs._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Ops.Arith.t_Rem t_usize t_usize =
  {
    f_Output = t_usize;
    f_rem_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_rem_post = (fun (self: t_usize) (rhs: t_usize) (out: t_usize) -> true);
    f_rem = fun (self: t_usize) (rhs: t_usize) -> C_usize (self._0 %! rhs._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Ops.Arith.t_Add t_usize t_usize =
  {
    f_Output = t_usize;
    f_add_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_add_post = (fun (self: t_usize) (rhs: t_usize) (out: t_usize) -> true);
    f_add = fun (self: t_usize) (rhs: t_usize) -> C_usize (self._0 +! rhs._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Ops.Arith.t_Div t_usize t_usize =
  {
    f_Output = t_usize;
    f_div_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_div_post = (fun (self: t_usize) (rhs: t_usize) (out: t_usize) -> true);
    f_div = fun (self: t_usize) (rhs: t_usize) -> C_usize (self._0 /! rhs._0) <: t_usize
  }

//////////////////////////

type u128 = t_u128
type u64 = t_u64
type u32 = t_u32
type u16 = t_u16
type u8 = t_u8
type usize = t_usize

type pub_u128 x = C_u128 { f_v = x }
type pub_u64 x = C_u64 { f_v = x }
type pub_u32 x = C_u32 { f_v = x }
type pub_u16 x = C_u16 { f_v = x }
type pub_u8 x = C_u8 { f_v = x }
type sz x = C_usize { f_v = x }
