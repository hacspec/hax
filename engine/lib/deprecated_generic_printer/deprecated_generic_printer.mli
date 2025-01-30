module Make (F : Features.T) (View : Concrete_ident.RENDER_API) : sig
  open Deprecated_generic_printer_base.Make(F)
  include API

  class print : print_class
end
