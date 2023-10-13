module Core.Marker

class t_Sized (h: Type) = {
  dummy_field: unit
}

(** we consider everything to be sized *)
instance t_Sized_all t: t_Sized t = {
  dummy_field = ()
}
