open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module Visitors = Ast_visitors.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  (* TODO: Swap to Concrete_ident see: https://github.com/hacspec/hax/issues/375 *)
  type analysis_data = concrete_ident list Map.M(String).t
  type id_order = int

  module Uprint =
    Ast_utils.MakeWithNamePolicy (F) (Concrete_ident.DefaultNamePolicy)

  let collect_concrete_idents =
    object
      inherit [_] Visitors.reduce as super
      inherit [_] U.Sets.Concrete_ident.monoid as m
      (* method visit_t _ _ = m#zero *)
      method visit_mutability (_f : unit -> _ -> _) (_env : unit) _ = m#zero

      method! visit_global_ident (env : unit) (x : Global_ident.t) =
        match x with
        | `Concrete x -> Set.singleton (module Concrete_ident) x
        | _ -> super#visit_global_ident env x

      method! visit_concrete_ident (_env : unit) (x : Concrete_ident.t) =
        Set.singleton (module Concrete_ident) x

      (* method! visit_App (env : unit) (f : A.expr) (args : A.expr list) (generic_args : A.generic_value list) (impl : A.impl_expr option) = *)
      (*   match impl with *)
      (*   | Some _ -> m#zero *)
      (*   | None -> super#visit_App env f args generic_args impl *)

      method! visit_ty (_env : unit) (_x : A.ty) = m#zero
      (* match x with *)
      (* | TApp _ | TAssociatedType _ | TOpaque _ -> m#zero *)
      (* | _ -> super#visit_ty env x *)

      (* method! visit_item env i = super#visit_item env i *)
    end

  let analyse (items : A.item list) : analysis_data =
    let temp_list = List.concat_map ~f:U.functions_of_item items in
    List.fold_left
      ~init:(Map.empty (module String))
      ~f:(fun y (name, body) ->
        Map.set y
          ~key:(Uprint.Concrete_ident_view.to_definition_name name)
          ~data:
            (Set.to_list (collect_concrete_idents#visit_expr () body)))
      temp_list
end
