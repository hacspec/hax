module Core.Marker

class t_Send (h: Type) = {
  dummy_field: unit
}

instance t_Send_all t: t_Send t = {
  dummy_field = ()
}

class t_Sync (h: Type) = {
  dummy_field: unit
}

instance t_Sync_all (h: Type): t_Sync t = {
  dummy_field: unit
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
