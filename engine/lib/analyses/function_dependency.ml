open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  type analysis_data = concrete_ident list Map.M(Concrete_ident).t
  type id_order = int

  let analyse_function_body (x : A.expr) : concrete_ident list =
    Set.to_list (U.Reducers.collect_concrete_idents#visit_expr () x)
  (* List.filter_map *)
  (*   ~f:(function *)
  (*     | `Projector (`Concrete cid) | `Concrete cid -> *)
  (*         Some (Uprint.Concrete_ident_view.to_definition_name cid) *)
  (*     | _ -> None) *)
  (*   (Set.to_list collect_global_idents) *)

  let functions_of_item (x : A.item) : (concrete_ident * A.expr) list =
    match x.v with
    | Fn { name; generics = _; body; params = _ } -> [ (name, body) ]
    | Impl { items; _ } ->
        List.filter_map
          ~f:(fun w ->
            match w.ii_v with
            | IIFn { body; params = _ } -> Some (w.ii_ident, body)
            | _ -> None)
          items
    | _ -> []

  let analyse (items : A.item list) : analysis_data =
    let temp_list = List.concat_map ~f:functions_of_item items in
    List.fold_left
      ~init:(Map.empty (module Concrete_ident))
      ~f:(fun y (name, body) ->
        Map.set y ~key:name ~data:(analyse_function_body body))
      temp_list
end
