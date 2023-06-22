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
      ((local_ident * A.ty) * int) list,
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
              ((name, items) :: fst y, count)
          | _ -> y)
        ~init:([], 0) items
    in
    let mut_map =
      List.fold_left
        ~f:(fun y x -> Map.set y ~key:(fst x) ~data:(snd x))
        ~init:(Map.empty (module GlobalIdent))
        mut_var_list
    in
    (* let key_list = Map.fold ~f:(fun ~key:k ~data:v -> fun a -> k :: a) ~init:[] (snd func_dep) in *)
    (* let lvl_list = Map.fold ~f:(fun ~key:k ~data:v -> fun a -> (k,v) :: a) ~init:[] (snd func_dep) in *)
    (* let lvl_sorted_list = List.map ~f:fst (List.sort ~compare:(fun (a, av) (b, bv) -> Int.compare av bv) lvl_list) in *)
    List.fold_left
      ~f:(fun y x ->
        Map.set y ~key:(fst x)
          ~data:
            (snd x
            @
            match Map.find (fst func_dep) (fst x) with
            | Some l -> List.concat (List.filter_map ~f:(Map.find mut_map) l)
            | None -> []))
      ~init:(Map.empty (module GlobalIdent))
      mut_var_list (* lvl_sorted_list *)

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
                   monadic;
                   lhs = { p = PBinding { mut = Mutable _; var; typ } };
                   rhs;
                   body;
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
