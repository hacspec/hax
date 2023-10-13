open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  type pre_data = unit

  type analysis_data =
    string list Map.M(String).t

  type id_order = int

  module Uprint =
    Ast_utils.MakeWithNamePolicy (F) (Concrete_ident.DefaultNamePolicy)

  let analyse_function_body (x : A.expr) :
    (* (Concrete_ident.t) *)
    string list =
    (* U.Reducers.collect_global_idents *)
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
      (List.filter_map
         ~f:(function
           | `Projector (`Concrete cid) | `Concrete cid -> Some (Uprint.Concrete_ident_view.to_definition_name cid) | _ -> None)
         (Set.to_list collect_global_idents))

  let analyse (_ : pre_data) (items : A.item list) : analysis_data =
    let temp_list =
      List.concat_map
        ~f:(fun x ->
          match x.v with
          | Fn { name; generics = _; body; params = _ } ->
              [ (Uprint.Concrete_ident_view.to_definition_name name, body) ]
          | Impl { generics = _; self_ty = _; of_trait = _ (* name, gen_vals *); items } ->
              List.filter_map
                ~f:(fun w ->
                  match w.ii_v with
                  | IIFn { body; params = _ } -> Some (Uprint.Concrete_ident_view.to_definition_name w.ii_ident, body)
                  | _ -> None)
                items
          | _ -> [])
        items
    in
    List.fold_left
      ~init:(Map.empty (module String))
      ~f:(fun y (name, body) ->
        Map.set y ~key:name ~data:(analyse_function_body body))
      temp_list
end
