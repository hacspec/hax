open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  open Ast

  type pre_data = unit

  type analysis_data =
    (global_ident, global_ident list, GlobalIdent.comparator_witness) Map.t
    * (global_ident, int, GlobalIdent.comparator_witness) Map.t

  module Flatten = Flatten_ast.Make (F)

  (* No recursion *)
  let rec flatten_map_index
      (map :
        (global_ident, global_ident list, GlobalIdent.comparator_witness) Map.t)
      (depth : int) (index : global_ident) : global_ident list * int =
    match Map.find map index with
    | Some l ->
        let a, b = flatten_concat_map map (depth + 1) l in
        (l @ a, b)
    | None -> ([], depth)

  and flatten_concat_map
      (map :
        (global_ident, global_ident list, GlobalIdent.comparator_witness) Map.t)
      (depth : int) (l : global_ident list) : global_ident list * int =
    let a, b = List.unzip (List.map ~f:(flatten_map_index map (depth + 1)) l) in
    (List.concat a, List.fold_left ~f:max ~init:0 b)

  let rec analyse (_ : pre_data) (items : A.item list) : analysis_data =
    let func_dep_list =
      List.filter_map
        ~f:(fun x ->
          match x.v with
          | Fn { name; generics; body; params } ->
              Some (name, analyse_function_body body)
          | _ -> None)
        items
    in
    let graph_map =
      List.fold_left
        ~f:(fun y x -> Map.set y ~key:(fst x) ~data:(snd x))
        ~init:(Map.empty (module GlobalIdent))
        func_dep_list
    in
    List.fold_left
      ~f:(fun y x ->
        let values, depth = flatten_concat_map graph_map 0 (snd x) in
        ( Map.set (fst y) ~key:(fst x)
            ~data:(Set.elements (Set.of_list (module GlobalIdent) values)),
          Map.set (snd y) ~key:(fst x) ~data:depth ))
      ~init:(Map.empty (module GlobalIdent), Map.empty (module GlobalIdent))
      func_dep_list

  and analyse_function_body (x : A.expr) : global_ident list =
    List.filter_map
      ~f:(fun x -> match x.e with GlobalVar g -> Some g | _ -> None)
      (Flatten.flatten_ast x)
end
