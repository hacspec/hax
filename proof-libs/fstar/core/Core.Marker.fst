
module Core.Marker

type t_PhantomData (t:Type0) = 
     | PhantomData: t_PhantomData t

class t_StructuralPartialEq (h: Type) = {
  dummy_structural_partial_eq_field: unit
}

class t_Send (h: Type) = {
  dummy_send_field: unit
}

(** we consider everything to be send *)
instance t_Send_all t: t_Send t = {
  dummy_send_field = ()
}

class t_Sync (h: Type) = {
  dummy_sync_field: unit
}

(** we consider everything to be sync *)
instance t_Sync_all t: t_Sync t = {
  dummy_sync_field = ()
}

class t_Sized (h: Type) = {
  dummy_field: unit
}

(** we consider everything to be sized *)
instance t_Sized_all t: t_Sized t = {
  dummy_field = ()
}

class t_Copy (h: Type) = {
  dummy_copy_field: unit
}

(** we consider everything to be copyable *)
instance t_Copy_all t: t_Copy t = {
  dummy_copy_field = ()
}

class t_Clone (h: Type) = {
  dummy_clone_field: unit
}

(** we consider everything to be clonable *)
instance t_Clone_all t: t_Clone t = {
  dummy_clone_field = ()
}
