open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  type id_order = int

  type pre_data =
    concrete_ident list Map.M(Concrete_ident).t
    * id_order Map.M(Concrete_ident).t

  type analysis_data =
    (local_ident list * (U.TypedLocalIdent.t * id_order) list)
    Map.M(Concrete_ident).t

  module Flatten = Flatten_ast.Make (F)

  let rec analyse (func_dep : pre_data) (items : A.item list) : analysis_data =
    let mut_var_list, _ =
      List.fold_left
        ~f:(fun y x ->
          match x.v with
          | Fn { name; generics; body; params } ->
              let items, count = analyse_function_body body (snd y) in
              ([ (name, items) ] @ fst y, count)
          | _ -> y)
        ~init:([], 0) items
    in
    let mut_map : (U.TypedLocalIdent.t * id_order) list Map.M(Concrete_ident).t
        =
      List.fold_left
        ~f:(fun y x -> Map.set y ~key:(fst x) ~data:(snd x))
        ~init:(Map.empty (module Concrete_ident))
        mut_var_list
    in
    List.fold_left
      ~f:(fun y x ->
        Map.set y ~key:x
          ~data:
            (let local_muts =
               match Map.find mut_map x with Some l -> l | None -> []
             in
             ( (List.map ~f:(fst >> fst) local_muts
               @
               match Map.find (fst func_dep) x with
               | Some l ->
                   let l' =
                     List.concat (List.filter_map ~f:(Map.find mut_map) l)
                   in
                   List.map ~f:(fst >> fst) l'
               | None -> []),
               local_muts )))
      ~init:(Map.empty (module Concrete_ident))
      (List.map ~f:fst mut_var_list)

  and analyse_function_body (x : A.expr) (i : id_order) :
      (U.TypedLocalIdent.t * id_order) list * id_order =
    let mut_var_list =
      Set.to_list
        ((object
            inherit [_] A.expr_reduce as super
            inherit [_] U.Sets.TypedLocalIdent.monoid as m
            method visit_t _ _ = m#zero
            method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

            method visit_expr s e =
              match e.e with
              | Assign { lhs = LhsLocalVar { var; typ }; witness } ->
                  Set.singleton (module U.TypedLocalIdent) (var, typ)
              | Let { lhs = { p = PBinding { mut = Mutable _; var; typ } }; _ }
                ->
                  Set.singleton (module U.TypedLocalIdent) (var, typ)
              | _ -> super#visit_expr s e
         end)
           #visit_expr
           () x)
    in
    number_list mut_var_list i

  (* State monad *)
  and number_list (l : 'a list) (i : int) : ('a * int) list * int =
    match l with
    | x :: xs ->
        let ys, i' = number_list xs (i + 1) in
        ((x, i) :: ys, i')
    | [] -> ([], i)
end
