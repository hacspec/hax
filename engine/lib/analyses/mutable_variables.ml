open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  type id_order = int

  (* TODO: Swap to Concrete_ident see: https://github.com/hacspec/hax/issues/375 *)
  type pre_data = concrete_ident list Map.M(String).t

  (* TODO: Swap to Concrete_ident see: https://github.com/hacspec/hax/issues/375 *)
  type analysis_data =
    (Local_ident.t list * (U.TypedLocalIdent.t * id_order) list)
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
        inherit ['s] VisitorsRuntime.monoid
        method zero : 's
        method plus : 's -> 's -> 's
      end

    class ['s, 't] prod_monoid (fst : 's monoid)
      (snd : 't monoid) (* : ['s * 't] monoid *) =
      object
        method fst = fst
        method snd = snd
        inherit ['s * 't] VisitorsRuntime.monoid
        method zero : 's * 't = (fst#zero, snd#zero)

        method plus : 's * 't -> 's * 't -> 's * 't =
          fst#plus *** snd#plus >> uncurry ( *** )
      end

    class ['s] set_monoid : ['s] monoid =
      object
        inherit ['s] VisitorsRuntime.monoid
        method zero = Set.empty (module W)
        method plus = Set.union
      end

    class ['s] map_monoid : ['s] monoid =
      object
        inherit ['s] VisitorsRuntime.monoid
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
           inherit [_] A.expr_reduce as super

           inherit
             [_, _] prod_monoid
               (object
                  inherit [_] set_monoid
               end)
               (object
                  inherit [_] map_monoid
               end) as m

           method visit_t _ _ = m#zero

           method visit_mutability (f : W.t list Map.M(Local_ident).t -> _ -> _)
               (ctx : W.t list Map.M(Local_ident).t) mu =
             match mu with Mutable wit -> f ctx wit | _ -> m#zero

           (* method! visit_PBinding env mut _ var _typ subpat = *)
           (*   m#plus *)
           (*     (m#plus *)
           (*        (match mut with *)
           (*         | Mutable _ -> *)
           (*           (Set.empty (module W), Map.singleton (module LocalIdent) var ([Identifier var])) *)
           (*         | _ -> m#zero) *)
           (*        (Option.value_map subpat ~default:m#zero *)
           (*           ~f:(fst >> super#visit_pat env))) *)
           (*     (Option.value_map (Map.find env var) ~default:m#zero ~f:(fun x -> (Set.of_list (module W) x, Map.empty (module LocalIdent)))) *)

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

           (* NO-OP? *)
           method! visit_global_ident (env : W.t list Map.M(Local_ident).t)
               (x : Global_ident.t) =
             match x with
             | `Concrete cid ->
                 Option.value_map ~default:m#zero
                   ~f:(fun (x, _) ->
                     ( Set.of_list
                         (module W)
                         (List.map ~f:(fun x -> W.Identifier x) x),
                       m#snd#zero ))
                   (Map.find data
                      (Uprint.Concrete_ident_view.to_definition_name cid))
             | _ -> super#visit_global_ident env x

           method! visit_concrete_ident (_env : W.t list Map.M(Local_ident).t)
               (cid : Concrete_ident.t) =
             Option.value_map ~default:m#zero
               ~f:(fun (x, _) ->
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
        (List.concat_map ~f:U.Destruct.Item.functions items)
    in
    let mut_map (* Concrete_ident *) :
        (Local_ident.t list * (U.TypedLocalIdent.t * id_order) list)
        Map.M(String).t =
      List.fold_left
        ~init:(Map.empty (module String (* Concrete_ident *)))
        ~f:(fun y (x_name, x_items) ->
          Map.set y
            ~key:(Uprint.Concrete_ident_view.to_definition_name x_name)
            ~data:
              ( List.map ~f:(fst >> fst) x_items
                @ Option.value_map ~default:[]
                    ~f:
                      (List.filter_map
                         ~f:
                           (Uprint.Concrete_ident_view.to_definition_name
                          >> Map.find y)
                      >> List.concat_map ~f:fst)
                    (Map.find func_dep
                       (Uprint.Concrete_ident_view.to_definition_name x_name)),
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
                | Immutable -> Set.empty (module U.TypedLocalIdent))
                (Option.value_map subpat ~default:m#zero
                   ~f:(fst >> super#visit_pat env))
         end)
           #visit_expr
           () x)
    in
    number_list mut_var_list i

  (* State monad *)
  and number_list (l : 'a list) (i : int) : ('a * int) list * int =
    List.fold_left ~init:([], i) ~f:(fun (y, i) x -> (y @ [ (x, i) ], i + 1)) l
end
