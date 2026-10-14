module Core_models.Marker
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::marker::Copy`]
class t_Copy (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Clone.t_Clone v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Copy v_Self|} -> i._super_i0

/// See [`std::marker::Send`]
class t_Send (v_Self: Type0) = { __marker_trait_t_Send:Prims.unit }

/// See [`std::marker::Sync`]
class t_Sync (v_Self: Type0) = { __marker_trait_t_Sync:Prims.unit }

/// See [`std::marker::StructuralPartialEq`]
class t_StructuralPartialEq (v_Self: Type0) = { __marker_trait_t_StructuralPartialEq:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_Send v_T = { __marker_trait_t_Send = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : t_Sync v_T = { __marker_trait_t_Sync = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
    : t_Copy v_T = { _super_i0 = FStar.Tactics.Typeclasses.solve }

type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T

/// See [`std::marker::PointeeSized`]
class t_PointeeSized (v_Self: Type0) = { __marker_trait_t_PointeeSized:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) : t_PointeeSized v_T = { __marker_trait_t_PointeeSized = () }

/// See [`std::marker::MetaSized`]
class t_MetaSized (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_PointeeSized v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_MetaSized v_Self|} -> i._super_i0

/// See [`std::marker::Sized`]
class t_Sized (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_MetaSized v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Sized v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) : t_MetaSized v_T = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : t_Sized v_T = { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::marker::Unsize`]
class t_Unsize (v_Self: Type0) (v_T: Type0) = { __marker_trait_t_Unsize:Prims.unit }

/// See [`std::marker::Freeze`]
class t_Freeze (v_Self: Type0) = { __marker_trait_t_Freeze:Prims.unit }

/// See [`std::marker::Unpin`]
class t_Unpin (v_Self: Type0) = { __marker_trait_t_Unpin:Prims.unit }

/// See [`std::marker::Destruct`]
class t_Destruct (v_Self: Type0) = { __marker_trait_t_Destruct:Prims.unit }

/// See [`std::marker::Tuple`]
class t_Tuple (v_Self: Type0) = { __marker_trait_t_Tuple:Prims.unit }

/// See [`std::marker::ConstParamTy_`]
class t_ConstParamTy_ (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_StructuralPartialEq v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_ConstParamTy_ v_Self|} -> i._super_i0

/// See [`std::marker::FnPtr`]
class t_FnPtr (v_Self: Type0) = { [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Copy v_Self }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_FnPtr v_Self|} -> i._super_i0

/// See [`std::marker::DiscriminantKind`]
class t_DiscriminantKind (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Discriminant:Type0
}

/// See [`std::marker::PhantomPinned`]
type t_PhantomPinned = | PhantomPinned : t_PhantomPinned
