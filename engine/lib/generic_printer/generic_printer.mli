module Make (F : Features.T) (View : Concrete_ident.VIEW_API) : sig
  open Generic_printer_base.Make(F)
  include API
end
