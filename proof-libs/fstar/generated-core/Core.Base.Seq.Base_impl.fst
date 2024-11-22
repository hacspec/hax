module Core.Base.Seq.Base_impl
#set-options "--fuel 1 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let (~.) = not

open Core.Cmp
open Core.Clone
open Core.Base.Int.Base_impl

let impl_2__is_empty
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
    : bool =
  match Core.Base.Seq.Base_spec.impl_1__match_list #v_T self with
  | Core.Base.Seq.LIST_NIL  -> true
  | Core.Base.Seq.LIST_CONS _ _ -> false

let impl_2__tl
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
    : Prims.Pure (Core.Base.Seq.t_Seq v_T)
      (requires ~.(impl_2__is_empty #v_T self <: bool))
      (fun _ -> Prims.l_True) =
  match Core.Base.Seq.Base_spec.impl_1__match_list #v_T self with
  | Core.Base.Seq.LIST_NIL  -> Core.Base.Seq.Base_spec.impl_1__NIL
  | Core.Base.Seq.LIST_CONS _ tl -> tl

let impl_2__hd__panic_cold_explicit (_: Prims.unit {False}) : Core.Panicking.t_Never =
  Core.Panicking.panic_explicit ()

let impl_2__hd
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
    : Prims.Pure v_T (requires ~.(impl_2__is_empty #v_T self <: bool)) (fun _ -> Prims.l_True) =
  match Core.Base.Seq.Base_spec.impl_1__match_list #v_T self with
  | Core.Base.Seq.LIST_NIL  ->
    Core.Panicking.never_to_any (impl_2__hd__panic_cold_explicit ()
        <:
        Core.Panicking.t_Never)
  | Core.Base.Seq.LIST_CONS hd _ -> hd

let impl_2__set_index__set_index_unary__panic_cold_explicit (_: Prims.unit {False})
    : Core.Panicking.t_Never = Core.Panicking.panic_explicit ()

let rec impl__eq_inner
      (#v_T: eqtype // Type0
    )
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialEq v_T v_T)
      (self other: Core.Base.Seq.t_Seq v_T)
    : bool =
  match
    Core.Base.Seq.Base_spec.impl_1__match_list #v_T
      (Core.Base.Seq.Base_spec.impl__clone #v_T self <: Core.Base.Seq.t_Seq v_T)
  with
  | Core.Base.Seq.LIST_NIL  ->
    impl_2__is_empty #v_T
      (Core.Base.Seq.Base_spec.impl__clone #v_T other <: Core.Base.Seq.t_Seq v_T)
  | Core.Base.Seq.LIST_CONS x xs ->
    match
      Core.Base.Seq.Base_spec.impl_1__match_list #v_T
        (Core.Base.Seq.Base_spec.impl__clone #v_T other <: Core.Base.Seq.t_Seq v_T)
    with
    | Core.Base.Seq.LIST_NIL  -> false
    | Core.Base.Seq.LIST_CONS y ys ->
    // let _ = (f_eq_pre x y) in
    // true
    x = y && impl__eq_inner #v_T #i1 #i2 xs ys

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T: eqtype)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Cmp.t_PartialEq v_T v_T)
    : Core.Cmp.t_PartialEq (Core.Base.Seq.t_Seq v_T) (Core.Base.Seq.t_Seq v_T) =
  {
    f_eq_pre = (fun (self: Core.Base.Seq.t_Seq v_T) (other: Core.Base.Seq.t_Seq v_T) -> true);
    f_eq_post
    =
    (fun (self: Core.Base.Seq.t_Seq v_T) (other: Core.Base.Seq.t_Seq v_T) (out: bool) -> true);
    f_eq
    =
    (fun x y -> x = y)
    // (fun (self: Core.Base.Seq.t_Seq v_T) (other: Core.Base.Seq.t_Seq v_T) ->
    //     impl__eq_inner #v_T self other)
  ;
    f_ne_pre = (fun (self: Core.Base.Seq.t_Seq v_T) (other: Core.Base.Seq.t_Seq v_T) -> true);
    f_ne_post
    =
    (fun (self: Core.Base.Seq.t_Seq v_T) (other: Core.Base.Seq.t_Seq v_T) (out: bool) -> true);
    f_ne
    =
    fun (self: Core.Base.Seq.t_Seq v_T) (other: Core.Base.Seq.t_Seq v_T) ->
      ~.(self = other
      // impl__eq_inner #v_T self other
  <: bool)
  }

let rec impl_2__len
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
    : Core.Base.Int.t_HaxInt =
  match Core.Base.Seq.Base_spec.impl_1__match_list #v_T self with
  | Core.Base.Seq.LIST_NIL  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Seq.LIST_CONS _ tl ->
    Core.Base.Int.Base_spec.impl_9__succ (impl_2__len #v_T tl <: Core.Base.Int.t_HaxInt)

let rec impl_2__rev_accum
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self accum: Core.Base.Seq.t_Seq v_T)
    : Core.Base.Seq.t_Seq v_T =
  match Core.Base.Seq.Base_spec.impl_1__match_list #v_T self with
  | Core.Base.Seq.LIST_NIL  -> accum
  | Core.Base.Seq.LIST_CONS hd tl ->
    impl_2__rev_accum #v_T
      tl
      (Core.Base.Seq.Base_spec.impl_1__cons #v_T accum hd <: Core.Base.Seq.t_Seq v_T)

let impl_2__rev
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
    : Core.Base.Seq.t_Seq v_T = impl_2__rev_accum #v_T self Core.Base.Seq.Base_spec.impl_1__NIL

let rec impl_2__get_index__get_index_unary
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (l: Core.Base.Seq.t_Seq v_T)
      (i: Core.Base.Int.t_Unary)
    : Prims.Pure v_T
      (requires i <. (impl_2__len #v_T l <: Core.Base.Int.t_HaxInt))
      (fun _ -> Prims.l_True) =
  match Core.Base.Int.Base_spec.impl_6__match_unary i with
  | Core.Base.Int.UNARY_ZERO  -> 
    impl_2__hd #v_T l
  | Core.Base.Int.UNARY_SUCC n ->
    impl_2__get_index__get_index_unary #v_T (impl_2__tl #v_T l <: Core.Base.Seq.t_Seq v_T) n

let impl_2__get_index
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
      (i: Core.Base.Int.t_HaxInt)
    : Prims.Pure v_T
      (requires i <. (impl_2__len #v_T self <: Core.Base.Int.t_HaxInt))
      (fun _ -> Prims.l_True) =
  impl_2__get_index__get_index_unary #v_T
    self
    (Core.Base.Int.Base_spec.impl_5__from_int i <: Core.Base.Int.t_Unary)

let rec impl_2__repeat__repeat_unary
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (n: Core.Base.Int.t_Unary)
      (v: v_T)
    : Core.Base.Seq.t_Seq v_T =
  match Core.Base.Int.Base_spec.impl_6__match_unary n with
  | Core.Base.Int.UNARY_ZERO  -> Core.Base.Seq.Base_spec.impl_1__NIL
  | Core.Base.Int.UNARY_SUCC m ->
    Core.Base.Seq.Base_spec.impl_1__cons #v_T
      (impl_2__repeat__repeat_unary #v_T
          m
          (// let _ = assume (f_clone_pre v) in
          // Core.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve
  v <: v_T)
        <:
        Core.Base.Seq.t_Seq v_T)
      v

let impl_2__repeat
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (n: Core.Base.Int.t_HaxInt)
      (v: v_T)
    : Core.Base.Seq.t_Seq v_T =
  impl_2__repeat__repeat_unary #v_T
    (Core.Base.Int.Base_spec.impl_5__from_int n <: Core.Base.Int.t_Unary)
    v

let rec impl_2__set_index__set_index_unary
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (x: Core.Base.Seq.t_Seq v_T)
      (i: Core.Base.Int.t_Unary)
      (v: v_T)
    : Prims.Pure (Core.Base.Seq.t_Seq v_T)
      (requires i <. (impl_2__len #v_T x <: Core.Base.Int.t_HaxInt))
      (fun _ -> Prims.l_True) =
  match Core.Base.Seq.Base_spec.impl_1__match_list #v_T x with
  | Core.Base.Seq.LIST_NIL  ->
    Core.Panicking.never_to_any (impl_2__set_index__set_index_unary__panic_cold_explicit ()
        <:
        Core.Panicking.t_Never)
  | Core.Base.Seq.LIST_CONS hd tl ->
    match Core.Base.Int.Base_spec.impl_6__match_unary i with
    | Core.Base.Int.UNARY_ZERO  -> Core.Base.Seq.Base_spec.impl_1__cons #v_T tl v
    | Core.Base.Int.UNARY_SUCC n ->
      Core.Base.Seq.Base_spec.impl_1__cons #v_T
        (impl_2__set_index__set_index_unary #v_T tl n v <: Core.Base.Seq.t_Seq v_T)
        hd

let impl_2__set_index
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Base.Seq.t_Seq v_T)
      (i: Core.Base.Int.t_HaxInt)
      (v: v_T)
    : Prims.Pure (Core.Base.Seq.t_Seq v_T)
      (requires i <. (impl_2__len #v_T self <: Core.Base.Int.t_HaxInt))
      (fun _ -> Prims.l_True) =
  impl_2__set_index__set_index_unary #v_T
    self
    (Core.Base.Int.Base_spec.impl_5__from_int i <: Core.Base.Int.t_Unary)
    v
