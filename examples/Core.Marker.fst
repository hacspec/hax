module Core.Marker

class t_Sized (h: Type) = {
  dummy_field: unit
}

instance t_Sized_all t: t_Sized t = {
  dummy_field = ()
}
