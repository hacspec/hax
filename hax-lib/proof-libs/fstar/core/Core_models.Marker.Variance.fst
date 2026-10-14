module Core_models.Marker.Variance
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::marker::Variance`]
class t_Variance (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Default.t_Default v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Variance v_Self|} -> i._super_i0

/// See [`std::marker::variance`]
let variance
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Variance v_T)
      (_: Prims.unit)
    : v_T = Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()

/// See [`std::marker::PhantomCovariant`]
type t_PhantomCovariant (v_T: Type0) =
  | PhantomCovariant : Core_models.Marker.t_PhantomData v_T -> t_PhantomCovariant v_T

/// See [`std::marker::PhantomContravariant`]
type t_PhantomContravariant (v_T: Type0) =
  | PhantomContravariant : Core_models.Marker.t_PhantomData v_T -> t_PhantomContravariant v_T

/// See [`std::marker::PhantomInvariant`]
type t_PhantomInvariant (v_T: Type0) =
  | PhantomInvariant : Core_models.Marker.t_PhantomData v_T -> t_PhantomInvariant v_T

/// See [`std::marker::PhantomCovariantLifetime`]
type t_PhantomCovariantLifetime =
  | PhantomCovariantLifetime : t_PhantomCovariant Prims.unit -> t_PhantomCovariantLifetime

/// See [`std::marker::PhantomContravariantLifetime`]
type t_PhantomContravariantLifetime =
  | PhantomContravariantLifetime : t_PhantomContravariant Prims.unit
    -> t_PhantomContravariantLifetime

/// See [`std::marker::PhantomInvariantLifetime`]
type t_PhantomInvariantLifetime =
  | PhantomInvariantLifetime : t_PhantomInvariant Prims.unit -> t_PhantomInvariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core_models.Marker.t_StructuralPartialEq t_PhantomCovariantLifetime =
  { __marker_trait_t_StructuralPartialEq = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core_models.Cmp.t_PartialEq t_PhantomCovariantLifetime t_PhantomCovariantLifetime =
  {
    f_eq_pre = (fun (self: t_PhantomCovariantLifetime) (other: t_PhantomCovariantLifetime) -> true);
    f_eq_post
    =
    (fun (self: t_PhantomCovariantLifetime) (other: t_PhantomCovariantLifetime) (out: bool) -> true);
    f_eq = fun (self: t_PhantomCovariantLifetime) (other: t_PhantomCovariantLifetime) -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core_models.Cmp.t_Eq t_PhantomCovariantLifetime =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core_models.Cmp.t_PartialOrd t_PhantomCovariantLifetime t_PhantomCovariantLifetime =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre
    =
    (fun (self: t_PhantomCovariantLifetime) (other: t_PhantomCovariantLifetime) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_PhantomCovariantLifetime)
        (other: t_PhantomCovariantLifetime)
        (out: Core_models.Option.t_Option Core_models.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_PhantomCovariantLifetime) (other: t_PhantomCovariantLifetime) ->
      Core_models.Option.Option_Some (Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering)
      <:
      Core_models.Option.t_Option Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core_models.Cmp.t_Ord t_PhantomCovariantLifetime =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_PhantomCovariantLifetime) (other: t_PhantomCovariantLifetime) -> true);
    f_cmp_post
    =
    (fun
        (self: t_PhantomCovariantLifetime)
        (other: t_PhantomCovariantLifetime)
        (out: Core_models.Cmp.t_Ordering)
        ->
        true);
    f_cmp
    =
    fun (self: t_PhantomCovariantLifetime) (other: t_PhantomCovariantLifetime) ->
      Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core_models.Hash.t_Hash t_PhantomCovariantLifetime =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomCovariantLifetime)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomCovariantLifetime)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
      (self: t_PhantomCovariantLifetime)
      (state: v_H)
      ->
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core_models.Marker.t_StructuralPartialEq t_PhantomContravariantLifetime =
  { __marker_trait_t_StructuralPartialEq = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core_models.Cmp.t_PartialEq t_PhantomContravariantLifetime
  t_PhantomContravariantLifetime =
  {
    f_eq_pre
    =
    (fun (self: t_PhantomContravariantLifetime) (other: t_PhantomContravariantLifetime) -> true);
    f_eq_post
    =
    (fun
        (self: t_PhantomContravariantLifetime)
        (other: t_PhantomContravariantLifetime)
        (out: bool)
        ->
        true);
    f_eq
    =
    fun (self: t_PhantomContravariantLifetime) (other: t_PhantomContravariantLifetime) -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core_models.Cmp.t_Eq t_PhantomContravariantLifetime =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core_models.Cmp.t_PartialOrd t_PhantomContravariantLifetime
  t_PhantomContravariantLifetime =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre
    =
    (fun (self: t_PhantomContravariantLifetime) (other: t_PhantomContravariantLifetime) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_PhantomContravariantLifetime)
        (other: t_PhantomContravariantLifetime)
        (out: Core_models.Option.t_Option Core_models.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_PhantomContravariantLifetime) (other: t_PhantomContravariantLifetime) ->
      Core_models.Option.Option_Some (Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering)
      <:
      Core_models.Option.t_Option Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core_models.Cmp.t_Ord t_PhantomContravariantLifetime =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre
    =
    (fun (self: t_PhantomContravariantLifetime) (other: t_PhantomContravariantLifetime) -> true);
    f_cmp_post
    =
    (fun
        (self: t_PhantomContravariantLifetime)
        (other: t_PhantomContravariantLifetime)
        (out: Core_models.Cmp.t_Ordering)
        ->
        true);
    f_cmp
    =
    fun (self: t_PhantomContravariantLifetime) (other: t_PhantomContravariantLifetime) ->
      Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core_models.Hash.t_Hash t_PhantomContravariantLifetime =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomContravariantLifetime)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomContravariantLifetime)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
      (self: t_PhantomContravariantLifetime)
      (state: v_H)
      ->
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core_models.Marker.t_StructuralPartialEq t_PhantomInvariantLifetime =
  { __marker_trait_t_StructuralPartialEq = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core_models.Cmp.t_PartialEq t_PhantomInvariantLifetime t_PhantomInvariantLifetime =
  {
    f_eq_pre = (fun (self: t_PhantomInvariantLifetime) (other: t_PhantomInvariantLifetime) -> true);
    f_eq_post
    =
    (fun (self: t_PhantomInvariantLifetime) (other: t_PhantomInvariantLifetime) (out: bool) -> true);
    f_eq = fun (self: t_PhantomInvariantLifetime) (other: t_PhantomInvariantLifetime) -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core_models.Cmp.t_Eq t_PhantomInvariantLifetime =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core_models.Cmp.t_PartialOrd t_PhantomInvariantLifetime t_PhantomInvariantLifetime =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre
    =
    (fun (self: t_PhantomInvariantLifetime) (other: t_PhantomInvariantLifetime) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_PhantomInvariantLifetime)
        (other: t_PhantomInvariantLifetime)
        (out: Core_models.Option.t_Option Core_models.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_PhantomInvariantLifetime) (other: t_PhantomInvariantLifetime) ->
      Core_models.Option.Option_Some (Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering)
      <:
      Core_models.Option.t_Option Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core_models.Cmp.t_Ord t_PhantomInvariantLifetime =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_PhantomInvariantLifetime) (other: t_PhantomInvariantLifetime) -> true);
    f_cmp_post
    =
    (fun
        (self: t_PhantomInvariantLifetime)
        (other: t_PhantomInvariantLifetime)
        (out: Core_models.Cmp.t_Ordering)
        ->
        true);
    f_cmp
    =
    fun (self: t_PhantomInvariantLifetime) (other: t_PhantomInvariantLifetime) ->
      Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core_models.Hash.t_Hash t_PhantomInvariantLifetime =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomInvariantLifetime)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomInvariantLifetime)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
      (self: t_PhantomInvariantLifetime)
      (state: v_H)
      ->
      state
  }

/// See [`std::marker::PhantomCovariant::new`]
let impl_39__new (#v_T: Type0) (_: Prims.unit) : t_PhantomCovariant v_T =
  PhantomCovariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
  <:
  t_PhantomCovariant v_T

/// See [`std::marker::PhantomCovariantLifetime::new`]
let impl__new (_: Prims.unit) : t_PhantomCovariantLifetime =
  PhantomCovariantLifetime (impl_39__new #Prims.unit ()) <: t_PhantomCovariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core_models.Default.t_Default t_PhantomCovariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomCovariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_Variance t_PhantomCovariantLifetime = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomCovariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomCovariant v_T) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      PhantomCovariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
      <:
      t_PhantomCovariant v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41 (#v_T: Type0) : t_Variance (t_PhantomCovariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46 (#v_T: Type0)
    : Core_models.Cmp.t_PartialEq (t_PhantomCovariant v_T) (t_PhantomCovariant v_T) =
  {
    f_eq_pre = (fun (self: t_PhantomCovariant v_T) (other: t_PhantomCovariant v_T) -> true);
    f_eq_post
    =
    (fun (self: t_PhantomCovariant v_T) (other: t_PhantomCovariant v_T) (out: bool) -> true);
    f_eq = fun (self: t_PhantomCovariant v_T) (other: t_PhantomCovariant v_T) -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47 (#v_T: Type0) : Core_models.Cmp.t_Eq (t_PhantomCovariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48 (#v_T: Type0)
    : Core_models.Cmp.t_PartialOrd (t_PhantomCovariant v_T) (t_PhantomCovariant v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_PhantomCovariant v_T) (other: t_PhantomCovariant v_T) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_PhantomCovariant v_T)
        (other: t_PhantomCovariant v_T)
        (out: Core_models.Option.t_Option Core_models.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_PhantomCovariant v_T) (other: t_PhantomCovariant v_T) ->
      Core_models.Option.Option_Some (Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering)
      <:
      Core_models.Option.t_Option Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49 (#v_T: Type0) : Core_models.Cmp.t_Ord (t_PhantomCovariant v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_PhantomCovariant v_T) (other: t_PhantomCovariant v_T) -> true);
    f_cmp_post
    =
    (fun
        (self: t_PhantomCovariant v_T)
        (other: t_PhantomCovariant v_T)
        (out: Core_models.Cmp.t_Ordering)
        ->
        true);
    f_cmp
    =
    fun (self: t_PhantomCovariant v_T) (other: t_PhantomCovariant v_T) ->
      Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50 (#v_T: Type0) : Core_models.Hash.t_Hash (t_PhantomCovariant v_T) =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomCovariant v_T)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomCovariant v_T)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
      (self: t_PhantomCovariant v_T)
      (state: v_H)
      ->
      state
  }

/// See [`std::marker::PhantomContravariant::new`]
let impl_51__new (#v_T: Type0) (_: Prims.unit) : t_PhantomContravariant v_T =
  PhantomContravariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
  <:
  t_PhantomContravariant v_T

/// See [`std::marker::PhantomContravariantLifetime::new`]
let impl_4__new (_: Prims.unit) : t_PhantomContravariantLifetime =
  PhantomContravariantLifetime (impl_51__new #Prims.unit ()) <: t_PhantomContravariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core_models.Default.t_Default t_PhantomContravariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomContravariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl_4__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_Variance t_PhantomContravariantLifetime =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomContravariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomContravariant v_T) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      PhantomContravariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
      <:
      t_PhantomContravariant v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53 (#v_T: Type0) : t_Variance (t_PhantomContravariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58 (#v_T: Type0)
    : Core_models.Cmp.t_PartialEq (t_PhantomContravariant v_T) (t_PhantomContravariant v_T) =
  {
    f_eq_pre = (fun (self: t_PhantomContravariant v_T) (other: t_PhantomContravariant v_T) -> true);
    f_eq_post
    =
    (fun (self: t_PhantomContravariant v_T) (other: t_PhantomContravariant v_T) (out: bool) -> true);
    f_eq = fun (self: t_PhantomContravariant v_T) (other: t_PhantomContravariant v_T) -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59 (#v_T: Type0) : Core_models.Cmp.t_Eq (t_PhantomContravariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60 (#v_T: Type0)
    : Core_models.Cmp.t_PartialOrd (t_PhantomContravariant v_T) (t_PhantomContravariant v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre
    =
    (fun (self: t_PhantomContravariant v_T) (other: t_PhantomContravariant v_T) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_PhantomContravariant v_T)
        (other: t_PhantomContravariant v_T)
        (out: Core_models.Option.t_Option Core_models.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_PhantomContravariant v_T) (other: t_PhantomContravariant v_T) ->
      Core_models.Option.Option_Some (Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering)
      <:
      Core_models.Option.t_Option Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61 (#v_T: Type0) : Core_models.Cmp.t_Ord (t_PhantomContravariant v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_PhantomContravariant v_T) (other: t_PhantomContravariant v_T) -> true);
    f_cmp_post
    =
    (fun
        (self: t_PhantomContravariant v_T)
        (other: t_PhantomContravariant v_T)
        (out: Core_models.Cmp.t_Ordering)
        ->
        true);
    f_cmp
    =
    fun (self: t_PhantomContravariant v_T) (other: t_PhantomContravariant v_T) ->
      Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62 (#v_T: Type0) : Core_models.Hash.t_Hash (t_PhantomContravariant v_T) =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomContravariant v_T)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomContravariant v_T)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
      (self: t_PhantomContravariant v_T)
      (state: v_H)
      ->
      state
  }

/// See [`std::marker::PhantomInvariant::new`]
let impl_63__new (#v_T: Type0) (_: Prims.unit) : t_PhantomInvariant v_T =
  PhantomInvariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
  <:
  t_PhantomInvariant v_T

/// See [`std::marker::PhantomInvariantLifetime::new`]
let impl_8__new (_: Prims.unit) : t_PhantomInvariantLifetime =
  PhantomInvariantLifetime (impl_63__new #Prims.unit ()) <: t_PhantomInvariantLifetime

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core_models.Default.t_Default t_PhantomInvariantLifetime =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomInvariantLifetime) -> true);
    f_default = fun (_: Prims.unit) -> impl_8__new ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: t_Variance t_PhantomInvariantLifetime = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_66 (#v_T: Type0) : Core_models.Default.t_Default (t_PhantomInvariant v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_PhantomInvariant v_T) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      PhantomInvariant (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_T)
      <:
      t_PhantomInvariant v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65 (#v_T: Type0) : t_Variance (t_PhantomInvariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_70 (#v_T: Type0)
    : Core_models.Cmp.t_PartialEq (t_PhantomInvariant v_T) (t_PhantomInvariant v_T) =
  {
    f_eq_pre = (fun (self: t_PhantomInvariant v_T) (other: t_PhantomInvariant v_T) -> true);
    f_eq_post
    =
    (fun (self: t_PhantomInvariant v_T) (other: t_PhantomInvariant v_T) (out: bool) -> true);
    f_eq = fun (self: t_PhantomInvariant v_T) (other: t_PhantomInvariant v_T) -> true
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_71 (#v_T: Type0) : Core_models.Cmp.t_Eq (t_PhantomInvariant v_T) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_72 (#v_T: Type0)
    : Core_models.Cmp.t_PartialOrd (t_PhantomInvariant v_T) (t_PhantomInvariant v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_PhantomInvariant v_T) (other: t_PhantomInvariant v_T) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: t_PhantomInvariant v_T)
        (other: t_PhantomInvariant v_T)
        (out: Core_models.Option.t_Option Core_models.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    fun (self: t_PhantomInvariant v_T) (other: t_PhantomInvariant v_T) ->
      Core_models.Option.Option_Some (Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering)
      <:
      Core_models.Option.t_Option Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_73 (#v_T: Type0) : Core_models.Cmp.t_Ord (t_PhantomInvariant v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_PhantomInvariant v_T) (other: t_PhantomInvariant v_T) -> true);
    f_cmp_post
    =
    (fun
        (self: t_PhantomInvariant v_T)
        (other: t_PhantomInvariant v_T)
        (out: Core_models.Cmp.t_Ordering)
        ->
        true);
    f_cmp
    =
    fun (self: t_PhantomInvariant v_T) (other: t_PhantomInvariant v_T) ->
      Core_models.Cmp.Ordering_Equal <: Core_models.Cmp.t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_74 (#v_T: Type0) : Core_models.Hash.t_Hash (t_PhantomInvariant v_T) =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomInvariant v_T)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
        (self: t_PhantomInvariant v_T)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Hash.t_Hasher v_H)
      (self: t_PhantomInvariant v_T)
      (state: v_H)
      ->
      state
  }
