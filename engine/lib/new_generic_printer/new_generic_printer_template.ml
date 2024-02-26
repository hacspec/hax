module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open Ast.Make (F)
  module P = New_generic_printer_base.Make (F)
  open PPrint

  let unimplemented s = string ("unimplemented: " ^ s)

  class print =
    object
      inherit P.base as _super
      method ty_TApp_tuple ~full:_ _args = unimplemented "ty_TApp_tuple"

      method ty_TApp_application ~full:_ _f _args =
        unimplemented "ty_TApp_application"

      method expr_App_constant ~full:_ _ident _generic_values =
        unimplemented "expr_App_constant"

      method expr_App_application ~full:_ _f _args _generics =
        unimplemented "expr_App_application"

      method expr_App_tuple_projection ~full:_ ~size:_ ~nth:_ _tuple =
        unimplemented "expr_App_tuple_projection"

      method expr_App_field_projection ~full:_ _ident _data =
        unimplemented "expr_App_field_projection"

      method expr_Construct_inductive ~full:_ ~is_record:_ ~is_struct:_
          ~constructor:_ ~base:_ _fields =
        unimplemented "expr_Construct_inductive"

      method expr_Construct_tuple ~full:_ _components =
        unimplemented "expr_Construct_tuple"

      method expr_ _ _ctx _expr = unimplemented "expr_"
      method ty_ _ _ctx _typ = unimplemented "ty_"
      method pat_ _ _ctx _pat = unimplemented "pat_"
      method item_ _ _item = unimplemented "item_"
      method arm_ _ _arm = unimplemented "arm_"
      method generic_param_ _ _gp = unimplemented "generic_param_"
      method param_ty_ _ _param_ty = unimplemented "param_ty_"
      method impl_item_ _ _ii = unimplemented "impl_item_"
      method trait_item_ _ _ti = unimplemented "trait_item_"
      method attr_ _ _attr = unimplemented "attr_"

      method namespace_of_concrete_ident =
        Concrete_ident.DefaultViewAPI.to_namespace

      method printer_name = "blank-template"
      method par_state _ = AlreadyPar

      method concrete_ident_ _ ~under_current_ns:_ _ident =
        unimplemented "concrete_ident_"
    end

  open New_generic_printer_api.Make (F)

  include Api (struct
    type aux_info = unit

    let new_print _ = (new print :> print_object)
  end)
end
