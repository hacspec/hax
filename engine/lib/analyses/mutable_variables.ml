open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  module Visitors = Ast_visitors.Make (F)
  open Ast

  type id_order = int

  (* TODO: Swap to Concrete_ident see: https://github.com/hacspec/hax/issues/375 *)
  type pre_data = concrete_ident list Map.M(String).t

  (* TODO: Swap to Concrete_ident see: https://github.com/hacspec/hax/issues/375 *)
  type analysis_data =
    (Local_ident.t list
    * Concrete_ident.t list
    * (U.TypedLocalIdent.t * id_order) list)
    (* external mut_vars and new variables (e.g. needs def / local) *)
    Map.M(String).t

  module Uprint =
    Ast_utils.MakeWithNamePolicy (F) (Concrete_ident.DefaultNamePolicy)

  module LocalIdentOrData (Ty : sig
    type ty [@@deriving compare, sexp]
  end) =
  struct
    module W = struct
      module T = struct
        type t = Data of Ty.ty | Identifier of Local_ident.t
        [@@deriving compare, sexp]
      end

      include T
      module C = Base.Comparator.Make (T)
      include C
    end

    include W
    include Set.M (W)

    class type ['s] monoid =
      object
        method zero : 's
        method plus : 's -> 's -> 's
      end

    class ['s, 't] prod_monoid (fst : 's monoid)
      (snd : 't monoid) (* : ['s * 't] monoid *) =
      object
        method fst = fst
        method snd = snd
        method zero : 's * 't = (fst#zero, snd#zero)

        method plus : 's * 't -> 's * 't -> 's * 't =
          fst#plus *** snd#plus >> uncurry ( *** )
      end

    class set_monoid : [(T.t, W.comparator_witness) Set.t] monoid =
      object
        method zero = Set.empty (module W)
        method plus = Set.union
      end

    class ['a] map_monoid :
      [(Local_ident.t, 'a list, Local_ident.comparator_witness) Map.t] monoid =
      object
        method zero = Map.empty (module Local_ident)

        method plus =
          let combine ~key:_ = ( @ ) in
          Map.merge_skewed ~combine
      end

    let analyse_expr (data : analysis_data)
        (env : W.t list Map.M(Local_ident).t) (expr : A.expr) :
        W.t list * W.t list Map.M(Local_ident).t =
      let mut_var_set, new_env =
        (object
           inherit [_] Visitors.reduce as super

           inherit
             [_, _] prod_monoid
               (object
                  inherit set_monoid
               end)
               (object
                  inherit [_] map_monoid
               end) as m

           (* method! visit_PBinding env mut _ var _typ subpat = *)
           (*   m#plus *)
           (*     (m#plus *)
           (*        (match mut with *)
           (*         | Mutable _ -> *)
           (*           (Set.empty (module W), Map.singleton (module Local_ident) var ([Identifier var])) *)
           (*         | _ -> m#zero) *)
           (*        (Option.value_map subpat ~default:m#zero *)
           (*           ~f:(fst >> super#visit_pat env))) *)
           (*     (Option.value_map (Map.find env var) ~default:m#zero ~f:(fun x -> (Set.of_list (module W) x, Map.empty (module Local_ident)))) *)

           method visit_Let env _monadic pat expr body =
             let new_set, new_env = super#visit_expr env expr in
             m#plus
               (super#visit_expr
                  (m#snd#plus (m#snd#plus env new_env)
                     (Map.of_alist_exn
                        (module Local_ident)
                        (List.map
                           ~f:(fun v -> (v, Set.to_list new_set))
                           (Set.to_list (U.Reducers.variables_of_pat pat)))))
                  body)
               (new_set, m#snd#zero)

           method! visit_local_ident (env : W.t list Map.M(Local_ident).t) ident
               =
             Option.value_map (Map.find env ident) ~default:m#zero ~f:(fun x ->
                 (Set.of_list (module W) x, m#snd#zero))

           (* (\* NO-OP? *\) *)
           (* method! visit_global_ident (env : W.t list Map.M(Local_ident).t) *)
           (*     (x : Global_ident.t) = *)
           (*   match x with *)
           (*   | `Concrete cid -> *)
           (*       Option.value_map ~default:m#zero *)
           (*         ~f:(fun (x, _) -> *)
           (*           ( Set.of_list *)
           (*               (module W) *)
           (*               (List.map ~f:(fun x -> W.Identifier x) x), *)
           (*             m#snd#zero )) *)
           (*         (Map.find data *)
           (*            (Uprint.Concrete_ident_view.to_definition_name cid)) *)
           (*   | _ -> super#visit_global_ident env x *)

           method! visit_concrete_ident (_env : W.t list Map.M(Local_ident).t)
               (cid : Concrete_ident.t) =
             Option.value_map ~default:m#zero
               ~f:(fun (x, _, _) ->
                 ( Set.of_list
                     (module W)
                     (List.map ~f:(fun x -> W.Identifier x) x),
                   m#snd#zero ))
               (Map.find data
                  (Uprint.Concrete_ident_view.to_definition_name cid))
        end)
          #visit_expr
          env expr
      in
      (Set.to_list mut_var_set, new_env)
  end

  let rec analyse (func_dep : pre_data) (items : A.item list) : analysis_data =
    let (mut_var_list, _)
          : (concrete_ident * (U.TypedLocalIdent.t * id_order) list) list * _ =
      List.fold_left ~init:([], 0)
        ~f:(fun (y, count) (name, body) ->
          let items, count = analyse_function_body body count in
          (y @ [ (name, items) ], count))
        (List.concat_map ~f:U.functions_of_item items)
    in
    let mut_map : analysis_data =
      List.fold_left
        ~init:(Map.empty (module String (* Concrete_ident *)) : analysis_data)
        ~f:(fun y (x_name, x_items) ->
          Map.set y
            ~key:(Uprint.Concrete_ident_view.to_definition_name x_name)
            ~data:
              (let local_items : Local_ident.t list =
                 List.map ~f:(fst >> fst) x_items
               in
               let dependent_items : Local_ident.t list =
                 Option.value_map ~default:[]
                   ~f:
                     (List.filter_map
                        ~f:
                          (Uprint.Concrete_ident_view.to_definition_name
                         >> Map.find y)
                     >> List.concat_map ~f:fst3)
                   (Map.find func_dep
                      (Uprint.Concrete_ident_view.to_definition_name x_name))
               in
               let trait_items : Concrete_ident.t list =
                 Option.value_map ~default:[]
                   ~f:
                     (List.fold_left ~init:[] ~f:(fun y x ->
                          y
                          @
                          if
                            match
                              String.chop_prefix ~prefix:"f_"
                                (Uprint.Concrete_ident_view.to_definition_name x)
                            with
                            | Some _ -> true
                            | None -> false
                            (* TODO: do better than string matching *)
                          then [ x ]
                          else []))
                   (Map.find func_dep
                      (Uprint.Concrete_ident_view.to_definition_name x_name))
               in
               (local_items @ dependent_items, trait_items, x_items)))
        mut_var_list
    in
    mut_map

  and analyse_function_body (x : A.expr) (i : id_order) :
      (U.TypedLocalIdent.t * id_order) list * id_order =
    let mut_var_list =
      Set.to_list
        ((object (self)
            inherit [_] Visitors.reduce as super
            inherit [_] U.Sets.TypedLocalIdent.monoid as m

            method! visit_pat' () pat' =
              match pat' with
              | PBinding { mut; var; typ; subpat; _ } ->
                  m#plus
                    (match mut with
                    | Mutable _ ->
                        Set.singleton (module U.TypedLocalIdent) (var, typ)
                    | Immutable -> Set.empty (module U.TypedLocalIdent))
                    (Option.value_map subpat ~default:m#zero
                       ~f:(fst >> self#visit_pat ()))
              | _ -> super#visit_pat' () pat'
         end)
           #visit_expr
           () x)
    in
    number_list mut_var_list i

  (* State monad *)
  and number_list (l : 'a list) (i : int) : ('a * int) list * int =
    List.fold_left ~init:([], i) ~f:(fun (y, i) x -> (y @ [ (x, i) ], i + 1)) l
end
