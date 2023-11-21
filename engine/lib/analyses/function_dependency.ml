open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  type analysis_data = concrete_ident list Map.M(String).t (* Concrete_ident *)
  type id_order = int

  module Uprint =
    Ast_utils.MakeWithNamePolicy (F) (Concrete_ident.DefaultNamePolicy)

  let analyse (items : A.item list) : analysis_data =
    let temp_list = List.concat_map ~f:U.functions_of_item items in
    List.fold_left
      ~init:(Map.empty (module String (* Concrete_ident *)))
      ~f:(fun y (name, body) ->
        Map.set y
          ~key:(Uprint.Concrete_ident_view.to_definition_name name)
          ~data:
            (Set.to_list
               (U.Reducers.collect_concrete_idents#visit_expr () body)))
      temp_list
end
