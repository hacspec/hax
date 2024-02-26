module Make (F : Features.T) : sig
  open New_generic_printer_api.Make(F)
  include API with type aux_info = unit
end
