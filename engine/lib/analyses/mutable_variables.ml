open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  open Ast

  type pre_data =
    (global_ident, global_ident list, GlobalIdent.comparator_witness) Map.t
    * (global_ident, int, GlobalIdent.comparator_witness) Map.t

  type analysis_data =
    ( global_ident,
      local_ident list * ((local_ident * A.ty) * int) list,
      GlobalIdent.comparator_witness )
    Map.t

  module Flatten = Flatten_ast.Make (F)

  let rec analyse (func_dep : pre_data) (items : A.item list) : analysis_data =
    let mut_var_list, _ =
      List.fold_left
        ~f:(fun y x ->
          match x.v with
          | Fn { name; generics; body; params } ->
              let items, count = analyse_function_body body (snd y) in
              (fst y @ [(name, items)], count)
          | _ -> y)
        ~init:([], 0) items
    in
    let mut_map : (global_ident,
                   ((local_ident * A.ty) * int) list,
                   GlobalIdent.comparator_witness) Map.t =
      List.fold_left
        ~f:(fun y x -> Map.set y ~key:(fst x) ~data:(snd x))
        ~init:(Map.empty (module GlobalIdent))
        mut_var_list
    in
    List.fold_left
      ~f:(fun y x ->
          Map.set y ~key:x
            ~data:
              (let local_muts =
                 match (Map.find mut_map x) with
                 | Some l -> l
                 | None -> []
               in
               (match Map.find (fst func_dep) x with
                | Some l ->
                  let l' = List.filter_map ~f:(Map.find y) l in
                  let b = List.concat (List.map ~f:fst l') in
                  List.map ~f:(fst >> fst) local_muts @ b
                | None -> []), local_muts))
      ~init:(Map.empty (module GlobalIdent))
      (List.map ~f:fst mut_var_list)

  and analyse_function_body (x : A.expr) (i : int) :
      ((local_ident * A.ty) * int) list * int =
    let mut_var_list =
      List.dedup_and_sort
        ~compare:(fun x y -> LocalIdent.compare (fst x) (fst y))
        (List.filter_map
           ~f:(fun x ->
             match x.e with
             | Assign { lhs = LhsLocalVar { var; typ }; witness } ->
               Some (var, typ)
             | Let
                 {
                   lhs = { p = PBinding { mut = Mutable _; var; typ } };
                   _
                 } ->
                 Some (var, typ)
             | _ -> None)
           (Flatten.flatten_ast x))
    in
    (* let unique_mut_var_list = *)
    number_list mut_var_list i

  (* State monad *)
  and number_list (l : 'a list) (i : int) : ('a * int) list * int =
    match l with
    | x :: xs ->
        let ys, i' = number_list xs (i + 1) in
        ((x, i) :: ys, i')
    | [] -> ([], i)
end
