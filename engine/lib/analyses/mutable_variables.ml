open! Prelude

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
            (* let name, items, count = analyse_item x (snd y) in *)
            (* ([(name, items)] @ fst y, count) *)
            match x.v with
            | Fn { name; generics = _; body; params = _ } ->
                let items, count = analyse_function_body body (snd y) in
                ([ (name, items) ] @ fst y, count)
            | Impl { generics = _; self_ty = _; of_trait = (_name, _gen_vals); items } ->
              List.fold_left
                ~f:(fun z w ->
                    match w.ii_v with
                    | IIFn { body; params = _ } ->
                      let items, count = analyse_function_body body (snd z) in
                      ([ ( w.ii_ident, items) ] @ fst z, count)
                    | _ -> z)
                ~init:y
                items
            | _ -> y
          )
        ~init:([], 0) items
    in
    let mut_map : (U.TypedLocalIdent.t * id_order) list Map.M(Concrete_ident).t
        =
      List.fold_left
        ~f:(fun y x -> Map.set y ~key:(fst x) ~data:(snd x))
        ~init:(Map.empty (module Concrete_ident))
        (mut_var_list)
    in
    List.fold_left
      ~f:(fun y x ->
        Map.set y ~key:x
          ~data:
            (let local_muts =
               match Map.find mut_map x with Some l -> l | None -> []
             in
             ( List.map ~f:(fst >> fst) (local_muts
                                         @
                                         match Map.find (fst func_dep) x with
                                         | Some l -> List.concat (List.filter_map ~f:(Map.find mut_map) l)
                                         | None -> []),
               local_muts )))
      ~init:(Map.empty (module Concrete_ident))
      (List.rev (List.map ~f:fst mut_var_list))

  and analyse_function_body (x : A.expr) (i : id_order) :
      (U.TypedLocalIdent.t * id_order) list * id_order =
    let mut_var_list =
      Set.to_list
        ((object
            inherit [_] A.expr_reduce as super
            inherit [_] U.Sets.TypedLocalIdent.monoid as m
            method visit_t _ _ = m#zero
            method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

            (* method visit_Assign env lhs _e _wit = *)
            (*   let rec visit_lhs lhs = *)
            (*     match lhs with *)
            (*     | A.LhsLocalVar { var; typ } -> *)
            (*         Set.singleton (module U.TypedLocalIdent) (var, typ) *)
            (*     | LhsFieldAccessor { e; _ } -> visit_lhs e *)
            (*     | LhsArrayAccessor { e; index; _ } -> *)
            (*         Set.union (super#visit_expr env index) (visit_lhs e) *)
            (*     | LhsArbitraryExpr { witness = _; e } -> *)
            (*         super#visit_expr env e (\* TODO? *\) *)
            (*   in *)
            (*   visit_lhs lhs *)

            method! visit_PBinding env mut _ var typ subpat =
              m#plus
                (match mut with
                | Mutable _ ->
                    Set.singleton (module U.TypedLocalIdent) (var, typ)
                | Immutable -> Set.empty (module U.TypedLocalIdent))
                (Option.value_map subpat ~default:m#zero
                   ~f:(fst >> super#visit_pat env))

            (* method visit_Let env _monadic pat expr body = *)
            (*    Set.union *)
            (*     (Set.union *)
            (*        (super#visit_expr env expr) *)
            (*        (super#visit_expr env body)) *)
            (*     (super#visit_pat env pat) *)
            (* (\* (match pat.p with *\) *)
            (* (\*  | PBinding { mut = Mutable _; var; typ } -> Set.singleton (module U.TypedLocalIdent) (var, typ) *\) *)
            (* (\*  | PAscription { (\\* typ; *\\) typ_span; pat = { p = PBinding { mut = Mutable _; var; typ } } } -> Set.singleton (module U.TypedLocalIdent) (var, typ) *\) *)
            (* (\*  | PDeref { subpat = { p = PBinding { mut = Mutable _; var; typ } }; witness } -> Set.singleton (module U.TypedLocalIdent) (var, typ) *\) *)
            (* (\*  (\\* | PBinding { mut = _; var; typ } -> Set.singleton (module U.TypedLocalIdent) (var, typ) *\\) *\) *)
            (* (\*  | _ -> Set.empty (module U.TypedLocalIdent)) *\) *)
         end)#visit_expr () x)
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
