module Core.Base.Seq
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let hd__panic_cold_explicit (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic_explicit ()

let set_index__set_index_unary__panic_cold_explicit (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic_explicit ()

let hd
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: Core.Base.Spec.Seq.t_Seq v_T)
    : Prims.Pure v_T (requires ~.(is_empty #v_T s <: bool)) (fun _ -> Prims.l_True) =
  match Core.Base.Spec.Seq.match_list #v_T s with
  | Core.Base.Spec.Seq.LIST_NIL  ->
    Rust_primitives.Hax.never_to_any (hd__panic_cold_explicit () <: Rust_primitives.Hax.t_Never)
  | Core.Base.Spec.Seq.LIST_CONS hd _ -> hd

let is_empty
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: Core.Base.Spec.Seq.t_Seq v_T)
    : bool =
  match Core.Base.Spec.Seq.match_list #v_T s with
  | Core.Base.Spec.Seq.LIST_NIL  -> true
  | Core.Base.Spec.Seq.LIST_CONS _ _ -> false

let tl
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: Core.Base.Spec.Seq.t_Seq v_T)
    : Prims.Pure (Core.Base.Spec.Seq.t_Seq v_T)
      (requires ~.(is_empty #v_T s <: bool))
      (fun _ -> Prims.l_True) =
  match Core.Base.Spec.Seq.match_list #v_T s with
  | Core.Base.Spec.Seq.LIST_NIL  -> Core.Base.Spec.Seq.nil #v_T ()
  | Core.Base.Spec.Seq.LIST_CONS _ tl -> tl

let rec eq_inner
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Cmp.t_PartialEq v_T v_T)
      (s other: Core.Base.Spec.Seq.t_Seq v_T)
    : bool =
  match
    Core.Base.Spec.Seq.match_list #v_T
      (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T) #FStar.Tactics.Typeclasses.solve s
        <:
        Core.Base.Spec.Seq.t_Seq v_T)
  with
  | Core.Base.Spec.Seq.LIST_NIL  ->
    is_empty #v_T
      (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T) #FStar.Tactics.Typeclasses.solve other
        <:
        Core.Base.Spec.Seq.t_Seq v_T)
  | Core.Base.Spec.Seq.LIST_CONS x xs ->
    match
      Core.Base.Spec.Seq.match_list #v_T
        (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T) #FStar.Tactics.Typeclasses.solve other
          <:
          Core.Base.Spec.Seq.t_Seq v_T)
    with
    | Core.Base.Spec.Seq.LIST_NIL  -> false
    | Core.Base.Spec.Seq.LIST_CONS y ys -> x =. y && eq_inner #v_T xs ys

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Cmp.t_PartialEq v_T v_T)
    : Core.Cmp.t_PartialEq (Core.Base.Spec.Seq.t_Seq v_T) (Core.Base.Spec.Seq.t_Seq v_T) =
  {
    f_eq_pre
    =
    (fun (self: Core.Base.Spec.Seq.t_Seq v_T) (other: Core.Base.Spec.Seq.t_Seq v_T) -> true);
    f_eq_post
    =
    (fun (self: Core.Base.Spec.Seq.t_Seq v_T) (other: Core.Base.Spec.Seq.t_Seq v_T) (out: bool) ->
        true);
    f_eq
    =
    (fun (self: Core.Base.Spec.Seq.t_Seq v_T) (other: Core.Base.Spec.Seq.t_Seq v_T) ->
        eq_inner #v_T
          (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T) #FStar.Tactics.Typeclasses.solve self
            <:
            Core.Base.Spec.Seq.t_Seq v_T)
          (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T) #FStar.Tactics.Typeclasses.solve other
            <:
            Core.Base.Spec.Seq.t_Seq v_T));
    f_ne_pre
    =
    (fun (self: Core.Base.Spec.Seq.t_Seq v_T) (other: Core.Base.Spec.Seq.t_Seq v_T) -> true);
    f_ne_post
    =
    (fun (self: Core.Base.Spec.Seq.t_Seq v_T) (other: Core.Base.Spec.Seq.t_Seq v_T) (out: bool) ->
        true);
    f_ne
    =
    fun (self: Core.Base.Spec.Seq.t_Seq v_T) (other: Core.Base.Spec.Seq.t_Seq v_T) ->
      ~.(eq_inner #v_T
          (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T) #FStar.Tactics.Typeclasses.solve self
            <:
            Core.Base.Spec.Seq.t_Seq v_T)
          (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T) #FStar.Tactics.Typeclasses.solve other
            <:
            Core.Base.Spec.Seq.t_Seq v_T)
        <:
        bool)
  }

let rec get_index__get_index_unary
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (l: Core.Base.Spec.Seq.t_Seq v_T)
      (i: Core.Base.Spec.Unary.t_Unary)
    : v_T =
  match Core.Base.Spec.Unary.match_unary i with
  | Core.Base.Spec.Unary.UNARY_ZERO  -> hd #v_T l
  | Core.Base.Spec.Unary.UNARY_SUCC n ->
    get_index__get_index_unary #v_T (tl #v_T l <: Core.Base.Spec.Seq.t_Seq v_T) n

let get_index
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: Core.Base.Spec.Seq.t_Seq v_T)
      (i: Core.Base.Spec.Haxint.t_HaxInt)
    : v_T =
  get_index__get_index_unary #v_T
    s
    (Core.Base.Spec.Unary.unary_from_int i <: Core.Base.Spec.Unary.t_Unary)

let rec len
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: Core.Base.Spec.Seq.t_Seq v_T)
    : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Seq.match_list #v_T s with
  | Core.Base.Spec.Seq.LIST_NIL  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Seq.LIST_CONS _ tl ->
    Core.Base.Spec.Haxint.succ (len #v_T tl <: Core.Base.Spec.Haxint.t_HaxInt)

let rec repeat__repeat_unary
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (n: Core.Base.Spec.Unary.t_Unary)
      (v: v_T)
    : Core.Base.Spec.Seq.t_Seq v_T =
  match Core.Base.Spec.Unary.match_unary n with
  | Core.Base.Spec.Unary.UNARY_ZERO  -> Core.Base.Spec.Seq.nil #v_T ()
  | Core.Base.Spec.Unary.UNARY_SUCC m ->
    Core.Base.Spec.Seq.cons #v_T
      (repeat__repeat_unary #v_T
          m
          (Core.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve v <: v_T)
        <:
        Core.Base.Spec.Seq.t_Seq v_T)
      v

let repeat
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (n: Core.Base.Spec.Haxint.t_HaxInt)
      (v: v_T)
    : Core.Base.Spec.Seq.t_Seq v_T =
  repeat__repeat_unary #v_T
    (Core.Base.Spec.Unary.unary_from_int n <: Core.Base.Spec.Unary.t_Unary)
    v

let rec rev__rev_accum
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s accum: Core.Base.Spec.Seq.t_Seq v_T)
    : Core.Base.Spec.Seq.t_Seq v_T =
  match Core.Base.Spec.Seq.match_list #v_T s with
  | Core.Base.Spec.Seq.LIST_NIL  -> accum
  | Core.Base.Spec.Seq.LIST_CONS hd tl ->
    rev__rev_accum #v_T tl (Core.Base.Spec.Seq.cons #v_T accum hd <: Core.Base.Spec.Seq.t_Seq v_T)

let rev
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: Core.Base.Spec.Seq.t_Seq v_T)
    : Core.Base.Spec.Seq.t_Seq v_T =
  rev__rev_accum #v_T s (Core.Base.Spec.Seq.nil #v_T () <: Core.Base.Spec.Seq.t_Seq v_T)

let rec set_index__set_index_unary
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (x: Core.Base.Spec.Seq.t_Seq v_T)
      (i: Core.Base.Spec.Unary.t_Unary)
      (v: v_T)
    : Core.Base.Spec.Seq.t_Seq v_T =
  match Core.Base.Spec.Seq.match_list #v_T x with
  | Core.Base.Spec.Seq.LIST_NIL  ->
    Rust_primitives.Hax.never_to_any (set_index__set_index_unary__panic_cold_explicit ()
        <:
        Rust_primitives.Hax.t_Never)
  | Core.Base.Spec.Seq.LIST_CONS hd tl ->
    match Core.Base.Spec.Unary.match_unary i with
    | Core.Base.Spec.Unary.UNARY_ZERO  -> Core.Base.Spec.Seq.cons #v_T tl v
    | Core.Base.Spec.Unary.UNARY_SUCC n ->
      Core.Base.Spec.Seq.cons #v_T
        (set_index__set_index_unary #v_T tl n v <: Core.Base.Spec.Seq.t_Seq v_T)
        hd

let set_index
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: Core.Base.Spec.Seq.t_Seq v_T)
      (i: Core.Base.Spec.Haxint.t_HaxInt)
      (v: v_T)
    : Prims.Pure (Core.Base.Spec.Seq.t_Seq v_T)
      (requires Core.Base.Pos.haxint_lt i (len #v_T s <: Core.Base.Spec.Haxint.t_HaxInt))
      (fun _ -> Prims.l_True) =
  set_index__set_index_unary #v_T
    s
    (Core.Base.Spec.Unary.unary_from_int i <: Core.Base.Spec.Unary.t_Unary)
    v
