open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  type analysis_data = concrete_ident list Map.M(Concrete_ident).t
  type id_order = int

  module Uprint =
    Ast_utils.MakeWithNamePolicy (F) (Concrete_ident.DefaultNamePolicy)

  let analyse_function_body (x : A.expr) : concrete_ident list =
    (* Set.to_list (U.Reducers.collect_concrete_idents#visit_expr () x) *)
    (* let collect_global_idents = (U.Reducers.collect_global_idents#visit_expr () x) in *)
    let collect_global_idents =
      (object
         inherit ['self] A.item_reduce as _super
         inherit [_] U.Sets.Global_ident.monoid as m
         method visit_t _ _ = m#zero

         method visit_mutability (f : unit -> _ -> _) () mu =
           match mu with Mutable wit -> f () wit | _ -> m#zero

         method! visit_global_ident (_env : unit) (x : Global_ident.t) =
           Set.singleton (module Global_ident) x
      end)
        #visit_expr
        () x
    in
    List.filter_map
      ~f:(function
        | `Projector (`Concrete cid) | `Concrete cid ->
            Some cid
        | _ -> None)
      (Set.to_list collect_global_idents)

  let analyse (items : A.item list) : analysis_data =
    let temp_list = List.concat_map ~f:U.functions_of_item items in
    List.fold_left
      ~init:(Map.empty (module Concrete_ident))
      ~f:(fun y (name, body) ->
        Map.set y ~key:name ~data:(analyse_function_body body))
      temp_list
end
