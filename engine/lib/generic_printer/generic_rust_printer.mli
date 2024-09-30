module Make (F : Features.T) : sig
  open Generic_printer_api.Make(F)
  include API with type aux_info = unit
end
