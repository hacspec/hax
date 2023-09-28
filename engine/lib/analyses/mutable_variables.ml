open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  type id_order = int

  type pre_data =
    concrete_ident list Map.M(Concrete_ident).t

  type analysis_data =
    (local_ident list * (U.TypedLocalIdent.t * id_order) list) (* external mut_vars vs new variables (e.g. needs def / local) *)
    Map.M(Concrete_ident).t

  module Flatten = Flatten_ast.Make (F)

  module Uprint =
    Ast_utils.MakeWithNamePolicy (F) (Concrete_ident.DefaultNamePolicy)

  let rec analyse (func_dep : pre_data) (items : A.item list) : analysis_data =
    let (mut_var_list, _) : (concrete_ident * (U.TypedLocalIdent.t * id_order) list) list * _ =
      (* (U.TypedLocalIdent.t * id_order) list * id_order *)
      List.fold_left
        ~f:(fun (y, count) x ->
          match x.v with
          | Fn { name; generics = _; body; params = _ } ->
              let items, count = analyse_function_body body count in
              ( y
                @ [
                    (name, items);
                  ],
                count )
          | Impl { generics = _; self_ty = _; of_trait = (_name, _gen_vals); items } ->
              List.fold_left
                ~f:(fun (z, count) w ->
                  match w.ii_v with
                  | IIFn { body; params = _ } ->
                      let items, count = analyse_function_body body count in
                      (* let extra_item, count = ([(LocalIdent.{ name = w.ii_name ^ "_loc"; id = LocalIdent.ty_param_id_of_int 0 (\* todo *\) }, body.typ), count] : (U.TypedLocalIdent.t * id_order) list), count + 1 in *)
                      (z @ [ (w.ii_ident, items (* @ extra_item *)) ], count)
                  | _ -> (z, count))
                ~init:(y, count) items
          | _ -> (y, count))
        ~init:([], 0) items
    in
    let mut_map :
        (local_ident list * (U.TypedLocalIdent.t * id_order) list)
        Map.M(Concrete_ident).t =
      List.fold_left
        ~init:(Map.empty (module Concrete_ident))
        ~f:(fun y (x_name, x_items) ->
          Map.set y ~key:x_name
            ~data:
              ( List.map ~f:(fst >> fst) x_items
                @ Option.value_map ~default:[]
                    ~f:
                      (List.filter_map ~f:(Map.find y) >> List.concat_map ~f:fst)
                    (Map.find func_dep x_name),
                x_items ))
        mut_var_list
    in
    mut_map

  and analyse_function_body (x : A.expr) (i : id_order) :
      (U.TypedLocalIdent.t * id_order) list * id_order =
    let mut_var_list =
      Set.to_list
        ((object
            inherit [_] A.expr_reduce as super
            inherit [_] U.Sets.TypedLocalIdent.monoid as m
            method visit_t _ _ = m#zero

            method visit_mutability (f : unit -> _ -> _) () mu =
              match mu with Mutable wit -> f () wit | _ -> m#zero

            method! visit_PBinding env mut _ var typ subpat =
              m#plus
                (match mut with
                | Mutable _ ->
                    Set.singleton (module U.TypedLocalIdent) (var, typ)
                | Immutable ->
                    (* Set.singleton (module U.TypedLocalIdent) (var, typ) *)
                    Set.empty (module U.TypedLocalIdent))
                (Option.value_map subpat ~default:m#zero
                   ~f:(fst >> super#visit_pat env))
         end)
           #visit_expr
           () x)
    in
    number_list mut_var_list i

  (* State monad *)
  and number_list (l : 'a list) (i : int) : ('a * int) list * int =
    List.fold_left ~init:([], i) ~f:(fun (y, i) x -> ((x, i) :: y, i + 1)) l
end
