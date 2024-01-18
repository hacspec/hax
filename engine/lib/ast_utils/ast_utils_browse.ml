open! Prelude
open Ast

type visit_level = ExprLevel | TypeLevel

module Mappers (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST

  let regenerate_span_ids =
    object
      inherit [_] item_map
      method visit_t () x = x
      method visit_mutability _ () m = m
      method visit_span = Fn.const Span.refresh_id
    end

  let normalize_borrow_mut =
    object
      inherit [_] expr_map as super
      method visit_t () x = x
      method visit_mutability _ () m = m

      method! visit_expr s e =
        let rec expr e =
          match e.e with
          | App
              {
                f = { e = GlobalVar (`Primitive Deref); _ };
                args = [ { e = Borrow { e = sub; _ }; _ } ];
                generic_args = _;
                impl = _;
              (* TODO: see issue #328 *)
              } ->
              expr sub
          | _ -> super#visit_expr s e
        in
        expr e
    end

  let rename_generic_constraints =
    object
      inherit [_] item_map as _super
      method visit_t _ x = x
      method visit_mutability _ _ m = m

      method! visit_GCType (s : (string, string) Hashtbl.t) bound id =
        let data = "i" ^ Int.to_string (Hashtbl.length s) in
        let _ = Hashtbl.add s ~key:id ~data in
        GCType { bound; id = data }

      method! visit_LocalBound s id =
        LocalBound { id = Hashtbl.find s id |> Option.value ~default:id }
    end

  let rename_local_idents (f : local_ident -> local_ident) =
    object
      inherit [_] item_map as _super
      method visit_t () x = x
      method visit_mutability _ () m = m
      method! visit_local_ident () ident = f ident
    end

  let rename_global_idents (f : visit_level -> global_ident -> global_ident) =
    object
      inherit [_] item_map as super
      method visit_t (_lvl : visit_level) x = x
      method visit_mutability _ (_lvl : visit_level) m = m
      method! visit_global_ident (lvl : visit_level) ident = f lvl ident
      method! visit_ty _ t = super#visit_ty TypeLevel t
      (* method visit_GlobalVar (lvl : level) i = GlobalVar (f lvl i) *)
    end

  let rename_concrete_idents
      (f : visit_level -> Concrete_ident.t -> Concrete_ident.t) =
    object
      inherit [_] item_map as super
      method visit_t (_lvl : visit_level) x = x
      method visit_mutability _ (_lvl : visit_level) m = m
      method! visit_concrete_ident (lvl : visit_level) ident = f lvl ident

      method! visit_global_ident lvl (x : Global_ident.t) =
        match x with
        | `Concrete x -> `Concrete (f lvl x)
        | _ -> super#visit_global_ident lvl x

      method! visit_ty _ t = super#visit_ty TypeLevel t
    end

  let rename_global_idents_item
      (f : visit_level -> global_ident -> global_ident) : item -> item =
    (rename_global_idents f)#visit_item ExprLevel

  module Destruct = Ast_utils_syntax.Destruct (F)

  (** Add type ascription nodes in nested function calls.  This helps
    type inference in the presence of associated types in backends
    that don't support them well (F* for instance). *)
  let add_typ_ascription =
    let is_app = Destruct.Expr.concrete_app' >> Option.is_some in
    let o =
      object
        inherit [_] item_map as super
        method visit_t (_ascribe_app : bool) x = x
        method visit_mutability _ (_ascribe_app : bool) m = m

        method! visit_expr' (ascribe_app : bool) e =
          (* Enable type ascription of underlying function
             application. In the F* backend, we're annotating every
             [Let] bindings, thus if we're facing a [Let], we turn
             off application ascription. Similarly, if we're facing
             an Ascription, we turn off application ascription. *)
          let ascribe_app =
            (ascribe_app || is_app e)
            && not ([%matches? Let _ | Ascription _] e)
          in
          super#visit_expr' ascribe_app e

        method! visit_expr (ascribe_app : bool) e =
          let e = super#visit_expr ascribe_app e in
          let ascribe (e : expr) =
            if [%matches? Ascription _] e.e then e
            else { e with e = Ascription { e; typ = e.typ } }
          in
          match e.e with
          | App
              {
                f = { e = GlobalVar (`Primitive Cast); _ } as f;
                args = [ arg ];
                generic_args;
                impl;
              } ->
              ascribe
                {
                  e with
                  e = App { f; args = [ ascribe arg ]; generic_args; impl };
                }
          | _ ->
              (* Ascribe the return type of a function application & constructors *)
              if (ascribe_app && is_app e.e) || [%matches? Construct _] e.e then
                ascribe e
              else e
      end
    in
    o#visit_item false
end

module Reducers (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST
  module TypedLocalIdent = Typed_local_ident.Make (F)

  module Sets = struct
    include Ast_utils_sets
    module TypedLocalIdent = M (TypedLocalIdent)
  end

  module Mappers = Mappers (F)

  let collect_local_idents =
    object
      inherit [_] item_reduce as _super
      inherit [_] Sets.Local_ident.monoid as m
      method visit_t _ _ = m#zero
      method visit_mutability (_f : unit -> _ -> _) () _ = m#zero
      method! visit_local_ident _ x = Set.singleton (module Local_ident) x
    end

  include struct
    open struct
      type env = Local_ident.t list

      let id_shadows ~(env : env) (id : Local_ident.t) =
        List.find env ~f:(fun x -> String.equal x.name id.name)
        |> Option.value ~default:id
        |> [%equal: Local_ident.t] id
        |> not

      let ( ++ ) = Set.union

      let shadows' (type a) ~env vars (x : a) next =
        (* account for shadowing within `vars` *)
        List.filter ~f:(id_shadows ~env:vars) (List.rev vars)
        |> Set.of_list (module Local_ident)
        |> Set.union (next (vars @ env) x)

      let shadows (type a) ~(env : env) (pats : pat list) (x : a)
          (next : env -> a -> Sets.Local_ident.t) =
        let vars =
          List.map pats ~f:(collect_local_idents#visit_pat ())
          |> Set.(union_list (module Local_ident) >> to_list)
        in
        shadows' ~env vars x next
    end

    let collect_ambiguous_local_idents =
      object (self)
        inherit [_] item_reduce as super
        inherit [_] Sets.Local_ident.monoid as m
        method visit_t (_ : env) _ = m#zero
        method visit_mutability (_f : env -> _ -> _) _ _ = m#zero

        method visit_arm' env { arm_pat; body } =
          shadows ~env [ arm_pat ] body super#visit_expr

        method visit_expr' env e =
          match e with
          | Let { monadic = _; lhs; rhs; body } ->
              super#visit_expr env rhs
              ++ shadows ~env [ lhs ] body super#visit_expr
          | Loop { kind; state; body; _ } ->
              let empty = Set.empty (module Local_ident) |> Fn.(id &&& id) in
              let ikind, ukind =
                match kind with
                | UnconditionalLoop -> empty
                | ForLoop { pat; it; _ } ->
                    ( collect_local_idents#visit_pat () pat,
                      super#visit_expr env it )
                | ForIndexLoop { start; end_; var; _ } ->
                    ( Set.singleton (module Local_ident) var,
                      super#visit_expr (var :: env) start
                      ++ super#visit_expr (var :: env) end_ )
              in
              let istate, ustate =
                match state with
                | Some { init; bpat; _ } ->
                    ( collect_local_idents#visit_pat () bpat,
                      super#visit_expr (Set.to_list ikind @ env) init )
                | _ -> empty
              in
              let intro = ikind ++ istate |> Set.to_list in
              ukind ++ ustate ++ shadows' ~env intro body super#visit_expr
          | Closure { params; body; _ } ->
              shadows ~env params body super#visit_expr
          | _ -> super#visit_expr' env e

        method visit_IIFn = self#visit_function_like
        method visit_Fn env _ _ = self#visit_function_like env

        method visit_function_like env body params =
          let f p = p.pat in
          shadows ~env (List.map ~f params) body super#visit_expr

        method visit_local_ident env id =
          Set.(if id_shadows ~env id then Fn.flip singleton id else empty)
            (module Local_ident)
      end

    let disambiguate_local_idents (item : item) =
      let ambiguous = collect_ambiguous_local_idents#visit_item [] item in
      let local_vars = collect_local_idents#visit_item () item |> ref in
      let refresh env (id : Local_ident.t) : string =
        let extract_suffix (id' : Local_ident.t) =
          String.chop_prefix ~prefix:(id.name ^ "_") id'.name
          |> Option.bind ~f:string_to_int
        in
        let suffix =
          Set.filter_map (module Int) env ~f:extract_suffix
          |> Set.max_elt |> Option.value ~default:0 |> ( + ) 1
        in
        id.name ^ "_" ^ Int.to_string suffix
      in
      let new_names =
        ambiguous |> Set.to_list
        |> List.map ~f:(fun (var : Local_ident.t) ->
               let var' = { var with name = refresh !local_vars var } in
               local_vars := Set.add !local_vars var';
               (var, var'))
        |> Map.of_alist_exn (module Local_ident)
      in
      let rename var = Map.find new_names var |> Option.value ~default:var in
      (Mappers.rename_local_idents rename)#visit_item () item
  end

  let collect_global_idents =
    object
      inherit ['self] item_reduce as _super
      inherit [_] Sets.Global_ident.monoid as m
      method visit_t _ _ = m#zero
      method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

      method! visit_global_ident (_env : unit) (x : Global_ident.t) =
        Set.singleton (module Global_ident) x
    end

  let collect_concrete_idents =
    object
      inherit ['self] item_reduce as super
      inherit [_] Sets.Concrete_ident.monoid as m
      method visit_t _ _ = m#zero
      method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

      method! visit_global_ident (_env : unit) (x : Global_ident.t) =
        match x with
        | `Concrete x -> Set.singleton (module Concrete_ident) x
        | _ -> super#visit_global_ident () x

      method! visit_concrete_ident (_env : unit) (x : Concrete_ident.t) =
        Set.singleton (module Concrete_ident) x
    end

  let variables_of_pat (p : pat) : Sets.Local_ident.t =
    (object
       inherit [_] expr_reduce as super
       inherit [_] Sets.Local_ident.monoid as m
       method visit_t _ _ = m#zero
       method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

       method! visit_PBinding env _ _ var _ subpat =
         m#plus
           (Set.singleton (module Local_ident) var)
           (Option.value_map subpat ~default:m#zero
              ~f:(fst >> super#visit_pat env))
    end)
      #visit_pat
      () p

  let variables_of_param (p : param) : Local_ident.t list =
    variables_of_pat p.pat |> Set.to_list

  let variables_of_pats : pat list -> Sets.Local_ident.t =
    List.map ~f:variables_of_pat >> Set.union_list (module Local_ident)

  let without_vars (mut_vars : Sets.TypedLocalIdent.t)
      (vars : Sets.Local_ident.t) =
    Set.filter mut_vars ~f:(fst >> Set.mem vars >> not)

  let without_pats_vars (mut_vars : Sets.TypedLocalIdent.t) :
      pat list -> Sets.TypedLocalIdent.t =
    variables_of_pats >> without_vars mut_vars

  let without_pat_vars (mut_vars : Sets.TypedLocalIdent.t) (pat : pat) :
      Sets.TypedLocalIdent.t =
    without_pats_vars mut_vars [ pat ]

  let free_assigned_variables
      (fv_of_arbitrary_lhs : F.arbitrary_lhs -> expr -> Sets.TypedLocalIdent.t)
      =
    object
      inherit [_] expr_reduce as super
      inherit [_] Sets.TypedLocalIdent.monoid as m
      method visit_t _ _ = m#zero
      method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

      (* TODO: loop state *)

      method visit_Assign _env lhs e _wit =
        let rec visit_lhs lhs =
          match lhs with
          | LhsLocalVar { var; _ } ->
              Set.singleton (module TypedLocalIdent) (var, e.typ)
          | LhsFieldAccessor { e; _ } -> visit_lhs e
          | LhsArrayAccessor { e; index; _ } ->
              Set.union (super#visit_expr () index) (visit_lhs e)
          | LhsArbitraryExpr { witness; e } -> fv_of_arbitrary_lhs witness e
        in
        visit_lhs lhs

      method visit_Match env scrut arms =
        List.fold_left ~init:(super#visit_expr env scrut) ~f:Set.union
        @@ List.map ~f:(fun arm -> super#visit_arm env arm) arms

      method visit_Let env _monadic pat expr body =
        Set.union (super#visit_expr env expr)
        @@ without_pat_vars (super#visit_expr env body) pat

      method visit_Closure env params body _captures =
        without_pats_vars (super#visit_expr env body) params

      method visit_Loop env body kind state _label _witness =
        let vars =
          (match kind with
          | UnconditionalLoop -> []
          | ForLoop { pat = _not_mutable; _ } -> []
          | ForIndexLoop { var = _not_mutable; _ } -> [])
          @ (state
            |> Option.map ~f:(fun { bpat; _ } -> variables_of_pat bpat)
            |> Option.to_list)
          |> Set.union_list (module Local_ident)
        in
        m#plus
          (super#visit_loop_kind env kind)
          (m#plus
             (Option.map ~f:(super#visit_loop_state env) state
             |> Option.value ~default:m#zero)
             (without_vars (super#visit_expr env body) vars))

      method visit_arm' env { arm_pat; body } =
        without_pat_vars (super#visit_expr env body) arm_pat
    end

  class ['s] expr_list_monoid =
    object
      inherit ['s] VisitorsRuntime.monoid
      method private zero = []
      method private plus = List.append
    end

  let collect_break_payloads =
    object
      inherit [_] expr_reduce as super
      inherit [_] expr_list_monoid as m
      method visit_t _ _ = m#zero
      method visit_mutability (_f : unit -> _ -> _) () _ = m#zero
      method visit_Break _ e _ _ = m#plus (super#visit_expr () e) [ e ]

      method visit_Loop _ _ _ _ _ _ = (* Do *NOT* visit sub nodes *)
                                      m#zero
    end
end
