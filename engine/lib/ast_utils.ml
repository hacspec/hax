open! Prelude
open Ast

type visit_level = ExprLevel | TypeLevel

module TypedLocalIdent (Ty : sig
  type ty [@@deriving show, yojson]
end) =
struct
  module T = struct
    type t = Local_ident.t * Ty.ty [@@deriving show, yojson]

    let sexp_of_t : t -> _ = fst >> Local_ident.sexp_of_t
    let compare (a : t) (b : t) = [%compare: Local_ident.t] (fst a) (fst b)
    let equal (a : t) (b : t) = [%eq: Local_ident.t] (fst a) (fst b)
  end

  include Base.Comparator.Make (T)
  include T
end

module UniqueList (T : sig
  type t [@@deriving eq, show, yojson]
  type comparator_witness
end) : sig
  type t [@@deriving eq, show, yojson]

  val without : T.t -> t -> t
  val cons : T.t -> t -> t
  val to_list : t -> T.t list
  val from_set : (T.t, T.comparator_witness) Set.t -> t
  val empty : t
  val is_empty : t -> bool
  val singleton : T.t -> t
end = struct
  type t = T.t list [@@deriving eq, show, yojson]

  let without x = List.filter ~f:([%eq: T.t] x >> not)
  let cons hd tl = hd :: tl
  let to_list = Fn.id
  let from_set s = Set.to_list s
  let empty = []
  let is_empty = List.is_empty
  let singleton x = [ x ]
end

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST
  module TypedLocalIdent = TypedLocalIdent (AST)
  module Visitors = Ast_visitors.Make (F)
  module M = Ast_builder.Make (F)
  module D = Ast_destruct.Make (F)

  module Expect = struct
    let mut_borrow (e : expr) : expr option =
      match e.e with Borrow { kind = Mut _; e; _ } -> Some e | _ -> None

    let borrow (e : expr) : expr option =
      match e.e with Borrow { e; _ } -> Some e | _ -> None

    let block (e : expr) : expr option =
      match e.e with Block { e; _ } -> Some e | _ -> None

    let deref (e : expr) : expr option =
      match e.e with
      | App { f = { e = GlobalVar (`Primitive Deref); _ }; args = [ e ]; _ } ->
          Some e
      | _ -> None

    let closure (e : expr) : (pat list * expr) option =
      match e.e with
      | Closure { params; body; _ } -> Some (params, body)
      | _ -> None

    let app (e : expr) :
        (expr
        * expr list
        * generic_value list
        * impl_expr option
        * impl_expr list)
        option =
      match e.e with
      | App { f; args; generic_args; trait; bounds_impls } ->
          (* TODO: propagate full trait *)
          Some (f, args, generic_args, Option.map ~f:fst trait, bounds_impls)
      | _ -> None

    let pbinding_simple (p : pat) : (local_ident * ty) option =
      match p.p with
      | PBinding { mut = Immutable; mode = _; var; typ; subpat = None } ->
          Some (var, typ)
      | _ -> None

    let concrete_app1 (f : Concrete_ident.name) (e : expr) : expr option =
      match e.e with
      | App
          {
            f = { e = GlobalVar (`Concrete f'); _ };
            args = [ e ];
            generic_args = _;
            trait = _;
            _;
            (* TODO: see issue #328 *)
          }
        when Concrete_ident.eq_name f f' ->
          Some e
      | _ -> None

    let deref_mut_app = concrete_app1 Core__ops__deref__DerefMut__deref_mut

    let local_var (e : expr) : expr option =
      match e.e with LocalVar _ -> Some e | _ -> None

    let arrow (typ : ty) : (ty list * ty) option =
      match typ with
      | TArrow (inputs, output) -> Some (inputs, output)
      | _ -> None

    let mut_ref (typ : ty) : ty option =
      match typ with TRef { mut = Mutable _; typ; _ } -> Some typ | _ -> None

    let concrete_app' : expr' -> concrete_ident option = function
      | App { f = { e = GlobalVar (`Concrete c); _ }; _ } -> Some c
      | _ -> None
  end

  module Sets = struct
    module Global_ident = struct
      include Set.M (Global_ident)

      class ['s] monoid =
        object
          method private zero = Set.empty (module Global_ident)
          method private plus = Set.union
        end
    end

    module Concrete_ident = struct
      include Set.M (Concrete_ident)

      class ['s] monoid =
        object
          method private zero = Set.empty (module Concrete_ident)
          method private plus = Set.union
        end
    end

    module Local_ident = struct
      include Set.M (Local_ident)

      class ['s] monoid =
        object
          method private zero = Set.empty (module Local_ident)
          method private plus = Set.union
        end
    end

    module TypedLocalIdent = struct
      include Set.M (TypedLocalIdent)

      let show (x : t) : string =
        [%show: TypedLocalIdent.t list] @@ Set.to_list x

      let pp (fmt : Stdlib.Format.formatter) (s : t) : unit =
        Stdlib.Format.pp_print_string fmt @@ show s

      class ['s] monoid =
        object
          method private zero = Set.empty (module TypedLocalIdent)
          method private plus = Set.union
        end
    end
  end

  let functions_of_item (x : item) : (concrete_ident * expr) list =
    match x.v with
    | Fn { name; generics = _; body; params = _; safety = _ } ->
        [ (name, body) ]
    | Impl { items; _ } ->
        List.filter_map
          ~f:(fun w ->
            match w.ii_v with
            | IIFn { body; params = _ } -> Some (w.ii_ident, body)
            | _ -> None)
          items
    | _ -> []

  module Mappers = struct
    let regenerate_span_ids =
      object
        inherit [_] Visitors.map
        method! visit_span () = Span.refresh_id
      end

    let normalize_borrow_mut =
      object
        inherit [_] Visitors.map as super

        method! visit_expr () e =
          let rec expr e =
            match e.e with
            | App
                {
                  f = { e = GlobalVar (`Primitive Deref); _ };
                  args = [ { e = Borrow { e = sub; _ }; _ } ];
                  generic_args = _;
                  trait = _;
                  _;
                  (* TODO: see issue #328 *)
                } ->
                expr sub
            | _ -> super#visit_expr () e
          in
          expr e
      end

    (** Rename impl expressions variables. By default, they are big
      and unique identifiers, after this function, they are renamed
      into `iN` where `N` is a short local unique identifier. *)
    let rename_generic_constraints =
      object
        inherit [_] Visitors.map as super

        method! visit_generic_constraint
            ((enabled, s) : bool * (string, string) Hashtbl.t) gc =
          match gc with
          | GCType { goal; name } when enabled ->
              let data = "i" ^ Int.to_string (Hashtbl.length s) in
              let _ = Hashtbl.add s ~key:name ~data in
              GCType { goal; name = data }
          | _ -> super#visit_generic_constraint (enabled, s) gc

        method! visit_trait_item (_, s) = super#visit_trait_item (true, s)

        method! visit_item' (_, s) item =
          let enabled =
            (* generic constraints on traits correspond to super
               traits, those are not local and should NOT be renamed *)
            [%matches? Trait _] item |> not
          in
          super#visit_item' (enabled, s) item

        method! visit_impl_expr_kind s ie =
          match ie with
          | LocalBound { id } ->
              LocalBound
                { id = Hashtbl.find (snd s) id |> Option.value ~default:id }
          | _ -> super#visit_impl_expr_kind s ie
      end

    let drop_bodies =
      object
        inherit [_] Visitors.map as super

        method! visit_item' () item' =
          match item' with
          | Fn { name; generics; body; params; safety } ->
              Fn
                {
                  name;
                  generics;
                  body = { body with e = GlobalVar (`TupleCons 0) };
                  params;
                  safety;
                }
          | _ -> super#visit_item' () item'
      end

    let replace_local_variables (map : (local_ident, expr, _) Map.t) =
      object
        inherit [_] Visitors.map as super

        method! visit_expr () e =
          match e.e with
          | LocalVar var -> Map.find map var |> Option.value ~default:e
          | _ -> super#visit_expr () e
      end

    (** [replace_local_variable var replacement] returns a visitor
      that maps any type of the AST replacing every occurence of the
      expression [LocalVar var] by [replacement]. *)
    let replace_local_variable (var : local_ident) (replacement : expr) =
      replace_local_variables
        (Map.of_alist_exn (module Local_ident) [ (var, replacement) ])

    let rename_local_idents (f : local_ident -> local_ident) =
      object
        inherit [_] Visitors.map as _super
        method! visit_local_ident () ident = f ident
      end

    let rename_global_idents (f : visit_level -> global_ident -> global_ident) =
      object
        inherit [_] Visitors.map as super
        method! visit_global_ident (lvl : visit_level) ident = f lvl ident
        method! visit_ty _ t = super#visit_ty TypeLevel t
      end

    let rename_concrete_idents
        (f : visit_level -> Concrete_ident.t -> Concrete_ident.t) =
      object
        inherit [_] Visitors.map as super
        method! visit_concrete_ident (lvl : visit_level) ident = f lvl ident

        method! visit_global_ident lvl (x : Global_ident.t) =
          match x with
          | `Concrete x -> `Concrete (f lvl x)
          | `Projector (`Concrete x) -> `Projector (`Concrete (f lvl x))
          | _ -> super#visit_global_ident lvl x

        method! visit_ty _ t = super#visit_ty TypeLevel t
      end

    let rename_global_idents_item
        (f : visit_level -> global_ident -> global_ident) : item -> item =
      (rename_global_idents f)#visit_item ExprLevel

    (** Add type ascription nodes in nested function calls.  This helps
    type inference in the presence of associated types in backends
    that don't support them well (F* for instance). *)
    let add_typ_ascription =
      let is_app = Expect.concrete_app' >> Option.is_some in
      let o =
        object
          inherit [_] Visitors.map as super

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
                  trait;
                  bounds_impls;
                } ->
                ascribe
                  {
                    e with
                    e =
                      App
                        {
                          f;
                          args = [ ascribe arg ];
                          generic_args;
                          trait;
                          bounds_impls;
                        };
                  }
            | _ ->
                (* Ascribe the return type of a function application & constructors *)
                if (ascribe_app && is_app e.e) || [%matches? Construct _] e.e
                then ascribe e
                else e
        end
      in
      o#visit_item false
  end

  module Reducers = struct
    let collect_local_idents =
      object
        inherit [_] Visitors.reduce as _super
        inherit [_] Sets.Local_ident.monoid as _m
        method! visit_local_ident () x = Set.singleton (module Local_ident) x
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

      (** Rust macros are hygienic: even if a macro introduces a name
         that already exists in scope, the compiler will not shadow
         it. Instead, it will track and differentiate the two, even if
         those have the same name. `collect_ambiguous_local_idents` is
         a visitor that collects such "fake" shadowings. *)
      let collect_ambiguous_local_idents =
        object (self)
          inherit [_] Visitors.reduce as super
          inherit [_] Sets.Local_ident.monoid as _m

          method! visit_arm' env { arm_pat; body; guard } =
            match guard with
            | None -> shadows ~env [ arm_pat ] body super#visit_expr
            | Some { guard = IfLet { lhs; rhs; _ }; _ } ->
                shadows ~env [ arm_pat ] rhs super#visit_expr
                ++ shadows ~env [ arm_pat; lhs ] body super#visit_expr

          method! visit_expr' env e =
            match e with
            | Let { monadic = _; lhs; rhs; body } ->
                super#visit_expr env rhs
                ++ shadows ~env [ lhs ] body super#visit_expr
            | Loop { kind; state; body; _ } ->
                let empty = Set.empty (module Local_ident) |> Fn.(id &&& id) in
                let ikind, ukind =
                  match kind with
                  | UnconditionalLoop -> empty
                  | WhileLoop { condition; _ } ->
                      ( collect_local_idents#visit_expr () condition,
                        super#visit_expr env condition )
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

          method! visit_impl_item' env ii =
            match ii with
            | IIFn { body; params } -> self#visit_function_like env body params
            | _ -> super#visit_impl_item' env ii

          method! visit_item' env i =
            match i with
            | Fn { body; params; _ } -> self#visit_function_like env body params
            | _ -> super#visit_item' env i

          method visit_function_like env body params =
            let f p = p.pat in
            shadows ~env (List.map ~f params) body super#visit_expr

          method! visit_local_ident env id =
            Set.(if id_shadows ~env id then Fn.flip singleton id else empty)
              (module Local_ident)
        end

      (** Rust macros are hygienic: even if a macro introduces a name
         that already exists in scope, the compiler will not shadow
         it. Instead, it will track and differentiate the two, even if
         those have the same name. `disambiguate_local_idents item`
         renames every instance of such a "fake" shadowing in
         `item`. See PR #368 for an example. *)
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
        inherit [_] Visitors.reduce as _super
        inherit [_] Sets.Global_ident.monoid as _m

        method! visit_global_ident (_env : unit) (x : Global_ident.t) =
          Set.singleton (module Global_ident) x
      end

    let collect_concrete_idents =
      object
        inherit [_] Visitors.reduce as super
        inherit [_] Sets.Concrete_ident.monoid as _m

        method! visit_global_ident (_env : unit) (x : Global_ident.t) =
          match x with
          | `Concrete x -> Set.singleton (module Concrete_ident) x
          | _ -> super#visit_global_ident () x

        method! visit_concrete_ident (_env : unit) (x : Concrete_ident.t) =
          Set.singleton (module Concrete_ident) x
      end

    let variables_of_pat (p : pat) : Sets.Local_ident.t =
      (object
         inherit [_] Visitors.reduce as super
         inherit [_] Sets.Local_ident.monoid as m

         method! visit_pat' env pat' =
           match pat' with
           | PBinding { var; subpat; _ } ->
               m#plus
                 (Set.singleton (module Local_ident) var)
                 (Option.value_map subpat ~default:m#zero
                    ~f:(fst >> super#visit_pat env))
           | _ -> super#visit_pat' env pat'
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
        (fv_of_arbitrary_lhs :
          F.arbitrary_lhs -> expr -> Sets.TypedLocalIdent.t) =
      object (self)
        inherit [_] Visitors.reduce as super
        inherit [_] Sets.TypedLocalIdent.monoid as m

        (* TODO: loop state *)

        method! visit_expr' () e =
          match e with
          | Assign { lhs; e; _ } ->
              let rec visit_lhs lhs =
                match lhs with
                | LhsLocalVar { var; _ } ->
                    Set.singleton (module TypedLocalIdent) (var, e.typ)
                | LhsFieldAccessor { e; _ } -> visit_lhs e
                | LhsArrayAccessor { e; index; _ } ->
                    Set.union (self#visit_expr () index) (visit_lhs e)
                | LhsArbitraryExpr { witness; e } ->
                    fv_of_arbitrary_lhs witness e
              in
              visit_lhs lhs
          | Match { scrutinee; arms } ->
              List.fold_left ~init:(self#visit_expr () scrutinee) ~f:Set.union
              @@ List.map ~f:(fun arm -> self#visit_arm () arm) arms
          | Let { lhs = pat; rhs = expr; body; _ } ->
              Set.union (self#visit_expr () expr)
              @@ without_pat_vars (self#visit_expr () body) pat
          | Closure { params; body; _ } ->
              without_pats_vars (self#visit_expr () body) params
          | Loop { body; kind; state; _ } ->
              let vars =
                (match kind with
                | UnconditionalLoop -> []
                | WhileLoop _ -> []
                | ForLoop { pat = _not_mutable; _ } -> []
                | ForIndexLoop { var = _not_mutable; _ } -> [])
                @ (state
                  |> Option.map ~f:(fun { bpat; _ } -> variables_of_pat bpat)
                  |> Option.to_list)
                |> Set.union_list (module Local_ident)
              in
              m#plus
                (self#visit_loop_kind () kind)
                (m#plus
                   (Option.map ~f:(self#visit_loop_state ()) state
                   |> Option.value ~default:m#zero)
                   (without_vars (self#visit_expr () body) vars))
          | _ -> super#visit_expr' () e

        method! visit_arm' () { arm_pat; body; guard } =
          match guard with
          | Some { guard = IfLet { lhs; rhs; _ }; _ } ->
              let rhs_vars =
                without_pat_vars (self#visit_expr () rhs) arm_pat
              in
              let body_vars =
                without_pats_vars (self#visit_expr () body) [ arm_pat; lhs ]
              in
              Set.union rhs_vars body_vars
          | None -> without_pat_vars (self#visit_expr () body) arm_pat
      end

    class ['s] expr_list_monoid =
      object
        method private zero = []
        method private plus = List.append
      end

    let collect_break_payloads =
      object (self)
        inherit [_] Visitors.reduce as super
        inherit [_] expr_list_monoid as _m

        method! visit_expr' () e =
          match e with
          | Break { e; _ } -> self#plus (self#visit_expr () e) [ e ]
          | Loop _ ->
              (* Do *NOT* visit sub nodes *)
              self#zero
          | _ -> super#visit_expr' () e
      end
  end

  (** Produces a local identifier which is locally fresh **with respect
      to variables {vars}**. *)
  let fresh_local_ident_in (vars : local_ident list) (prefix : string) :
      Local_ident.t =
    let free_suffix =
      vars
      |> List.filter_map ~f:(fun ({ name; _ } : local_ident) ->
             String.chop_prefix ~prefix name)
      |> List.map ~f:(function "" -> "0" | s -> s)
      |> List.filter_map ~f:Stdlib.int_of_string_opt
      |> List.fold ~init:(-1) ~f:Int.max
      |> ( + ) 1
      |> function
      | 0 -> ""
      | n -> Int.to_string n
    in
    {
      name = prefix ^ free_suffix;
      id =
        (* TODO: freshness is local and name-only here... *)
        Local_ident.mk_id Expr (-1);
    }

  (** Produces a local identifier which is locally fresh **with respect
      to expressions {exprs}**. *)
  let fresh_local_ident_in_expr (exprs : expr list) (prefix : string) :
      Local_ident.t =
    fresh_local_ident_in
      (List.map ~f:(Reducers.collect_local_idents#visit_expr ()) exprs
      |> Set.union_list (module Local_ident)
      |> Set.to_list)
      prefix

  let never_typ : ty =
    let ident =
      `Concrete (Concrete_ident.of_name Type Rust_primitives__hax__Never)
    in
    TApp { ident; args = [] }

  let is_never_typ : ty -> bool = function
    | TApp { ident; _ } ->
        Global_ident.eq_name Rust_primitives__hax__Never ident
    | _ -> false

  let unit_typ : ty = TApp { ident = `TupleType 0; args = [] }

  let unit_expr span : expr =
    { typ = unit_typ; span; e = GlobalVar (`TupleCons 0) }

  (* TODO: Those tuple1 things are wrong! Tuples of size one exists in Rust! e.g. `(123,)` *)
  let rec remove_tuple1_pat (p : pat) : pat =
    match p.p with
    | PConstruct { constructor = `TupleType 1; fields = [ { pat; _ } ]; _ } ->
        remove_tuple1_pat pat
    | _ -> p

  let rec remove_tuple1 (t : ty) : ty =
    match t with
    | TApp { ident = `TupleType 1; args = [ GType t ] } -> remove_tuple1 t
    | _ -> t

  let remove_unsize (e : expr) : expr =
    match e.e with
    | App { f = { e = GlobalVar f; _ }; args = [ e ]; _ }
      when Global_ident.eq_name Rust_primitives__unsize f ->
        e
    | _ -> e

  (** See [beta_reduce_closure]'s documentation. *)
  let beta_reduce_closure_opt (e : expr) : expr option =
    let* f, args, _, _, _ = Expect.app e in
    let* pats, body = Expect.closure f in
    let* vars = List.map ~f:Expect.pbinding_simple pats |> sequence in
    let vars = List.map ~f:fst vars in
    let replacements =
      List.zip_exn vars args |> Map.of_alist_exn (module Local_ident)
    in
    Some ((Mappers.replace_local_variables replacements)#visit_expr () body)

  (** Reduces a [(|x1, ..., xN| body)(e1, ..., eN)] to [body[x1/e1, ..., xN/eN]].
        This assumes the arities are right: [(|x, y| ...)(e1)]. *)
  let beta_reduce_closure (e : expr) : expr =
    beta_reduce_closure_opt e |> Option.value ~default:e

  let is_unit_typ : ty -> bool =
    remove_tuple1 >> [%matches? TApp { ident = `TupleType 0; _ }]

  let rec pat_is_expr (p : pat) (e : expr) =
    match (p.p, e.e) with
    | _, Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; _ } ->
        pat_is_expr p e
    | PBinding { subpat = None; var = pv; _ }, LocalVar ev ->
        [%eq: local_ident] pv ev
    | ( PConstruct { constructor = pn; fields = pargs; _ },
        Construct { constructor = en; fields = eargs; base = None; _ } )
      when [%eq: global_ident] pn en -> (
        match List.zip pargs eargs with
        | Ok zip ->
            List.for_all
              ~f:(fun (x, y) ->
                [%eq: global_ident] x.field (fst y) && pat_is_expr x.pat (snd y))
              zip
        | Unequal_lengths -> false)
    | _ -> false

  let make_let (lhs : pat) (rhs : expr) (body : expr) =
    if pat_is_expr lhs body then rhs
    else { body with e = Let { monadic = None; lhs; rhs; body } }

  let make_lets (lbs : (pat * expr) list) (body : expr) =
    List.fold_right ~init:body
      ~f:(fun (pat, expr) body -> make_let pat expr body)
      lbs

  let make_var_pat (var : local_ident) (typ : ty) (span : span) : pat =
    {
      p = PBinding { mut = Immutable; mode = ByValue; var; typ; subpat = None };
      span;
      typ;
    }

  let ty_equality (a : ty) (b : ty) : bool =
    let replace_spans =
      object
        inherit [_] Visitors.map
        method! visit_span _ = function _ -> Span.default
      end
    in
    let a = replace_spans#visit_ty () a in
    let b = replace_spans#visit_ty () b in
    [%eq: ty] a b

  let let_of_binding ((var, rhs) : local_ident * expr) (body : expr) : expr =
    make_let (make_var_pat var rhs.typ rhs.span) rhs body

  let lets_of_bindings (bindings : (local_ident * expr) list) (body : expr) :
      expr =
    List.fold_right ~init:body ~f:let_of_binding bindings

  let make_tuple_typ' (tuple : ty list) : ty =
    TApp
      {
        ident = `TupleType (List.length tuple);
        args = List.map ~f:(fun typ -> GType typ) tuple;
      }

  let make_tuple_typ (tuple : ty list) : ty =
    match tuple with [ ty ] -> ty | _ -> make_tuple_typ' tuple

  let make_unit_param (span : span) : param =
    let typ = unit_typ in
    let pat = M.pat_PWild ~typ ~span in
    { pat; typ; typ_span = None; attrs = [] }

  let make_seq (e1 : expr) (e2 : expr) : expr =
    make_let (M.pat_PWild ~typ:e1.typ ~span:e1.span) e1 e2

  let make_tuple_field_pat (len : int) (nth : int) (pat : pat) : field_pat =
    { field = `TupleField (nth + 1, len); pat }

  let make_tuple_pat'' span (tuple : field_pat list) : pat =
    match tuple with
    | [ { pat; _ } ] -> pat
    | _ ->
        let len = List.length tuple in
        {
          p =
            PConstruct
              {
                constructor = `TupleCons len;
                is_record = false;
                is_struct = true;
                fields = tuple;
              };
          typ = make_tuple_typ @@ List.map ~f:(fun { pat; _ } -> pat.typ) tuple;
          span;
        }

  let make_tuple_pat' (pats : pat list) : pat =
    let len = List.length pats in
    let span = Span.union_list @@ List.map ~f:(fun p -> p.span) pats in
    List.mapi ~f:(fun i pat -> { field = `TupleField (i, len); pat }) pats
    |> make_tuple_pat'' span

  let make_tuple_pat : pat list -> pat = function
    | [ pat ] -> pat
    | pats -> make_tuple_pat' pats

  let make_tuple_expr' ~(span : span) (tuple : expr list) : expr =
    let len = List.length tuple in
    {
      e =
        Construct
          {
            constructor = `TupleCons len;
            is_record = false;
            is_struct = true;
            fields =
              List.mapi ~f:(fun i x -> (`TupleField (i, len), x)) @@ tuple;
            base = None;
          };
      typ = make_tuple_typ @@ List.map ~f:(fun { typ; _ } -> typ) tuple;
      span;
    }

  let make_tuple_expr ~(span : span) : expr list -> expr = function
    | [ e ] -> e
    | es -> make_tuple_expr' ~span es

  (* maybe we should just drop Construct in favor of a
     [Record] thing, and put everything which is not a Record
       into an App. This would simplify stuff quite much. Maybe not
       for LHS things. *)
  let call_Constructor' (constructor : global_ident) is_struct
      (args : expr list) span ret_typ =
    let mk_field =
      let len = List.length args in
      fun n -> `TupleField (len, n)
    in
    let fields = List.mapi ~f:(fun i arg -> (mk_field i, arg)) args in
    {
      e =
        Construct
          { constructor; is_record = false; is_struct; fields; base = None };
      typ = ret_typ;
      span;
    }

  let call_Constructor (constructor_name : Concrete_ident.name)
      (is_struct : bool) (args : expr list) span ret_typ =
    call_Constructor'
      (`Concrete
        (Concrete_ident.of_name (Constructor { is_struct }) constructor_name))
      is_struct args span ret_typ

  let call' ?impl f ?(generic_args = []) ?(impl_generic_args = [])
      (args : expr list) span ret_typ =
    let typ = TArrow (List.map ~f:(fun arg -> arg.typ) args, ret_typ) in
    let e = GlobalVar f in
    {
      e =
        App
          {
            f = { e; typ; span };
            args;
            generic_args;
            bounds_impls = [];
            trait = Option.map ~f:(fun impl -> (impl, impl_generic_args)) impl;
          };
      typ = ret_typ;
      span;
    }

  let call ?(kind : Concrete_ident.Kind.t = Value) ?(generic_args = [])
      ?(impl_generic_args = []) ?impl (f_name : Concrete_ident.name)
      (args : expr list) span ret_typ =
    call' ?impl ~generic_args ~impl_generic_args
      (`Concrete (Concrete_ident.of_name kind f_name))
      args span ret_typ

  let make_closure (params : pat list) (body : expr) (span : span) : expr =
    let params =
      match params with
      | [] -> [ M.pat_PWild ~typ:unit_typ ~span ]
      | _ -> params
    in
    let e = Closure { params; body; captures = [] } in
    { e; typ = TArrow (List.map ~f:(fun p -> p.typ) params, body.typ); span }

  let string_lit span (s : string) : expr =
    { span; typ = TStr; e = Literal (String s) }

  let hax_failure_expr' span (typ : ty) (context, kind) (ast : string) =
    let error = Diagnostics.pretty_print_context_kind context kind in
    let args = List.map ~f:(string_lit span) [ error; ast ] in
    call Rust_primitives__hax__failure args span typ

  let hax_failure_expr span (typ : ty) (context, kind) (expr0 : Ast.Full.expr) =
    hax_failure_expr' span typ (context, kind) (Print_rust.pexpr_str expr0)

  let hax_failure_typ =
    let ident =
      `Concrete (Concrete_ident.of_name Type Rust_primitives__hax__failure)
    in
    TApp { ident; args = [] }

  module LiftToFullAst = struct
    let expr : AST.expr -> Ast.Full.expr = Stdlib.Obj.magic
    let ty : AST.ty -> Ast.Full.ty = Stdlib.Obj.magic
    let item : AST.item -> Ast.Full.item = Stdlib.Obj.magic
  end

  module Debug : sig
    val expr : ?label:string -> AST.expr -> unit
    (** Prints an expression pretty-printed as Rust, with its full
        AST encoded as JSON, available as a file, so that one can
        `jless` or `jq` into it. *)
  end = struct
    let expr ?(label = "") (e : AST.expr) : unit =
      let path = tempfile_path ~suffix:".json" in
      Core.Out_channel.write_all path
        ~data:([%yojson_of: AST.expr] e |> Yojson.Safe.pretty_to_string);
      let e = LiftToFullAst.expr e in
      "```rust " ^ label ^ "\n" ^ Print_rust.pexpr_str e
      ^ "\n```\x1b[34m JSON-encoded AST available at \x1b[1m" ^ path
      ^ "\x1b[0m (hint: use `jless " ^ path ^ "`)"
      |> Stdio.prerr_endline
  end

  let unbox_expr' (next : expr -> expr) (e : expr) : expr =
    match e.e with
    | App { f = { e = GlobalVar f; _ }; args = [ e ]; _ }
      when Global_ident.eq_name Alloc__boxed__Impl__new f ->
        next e
    | _ -> e

  let underef_expr' (next : expr -> expr) (e : expr) : expr =
    match e.e with
    | App
        {
          f = { e = GlobalVar (`Primitive Ast.Deref); _ };
          args = [ e ];
          generic_args = _;
          bounds_impls = _;
          trait = _;
        } ->
        next e
    | _ -> e

  let rec unbox_expr e = unbox_expr' unbox_expr e
  let underef_expr e = underef_expr' unbox_expr e

  let rec unbox_underef_expr e =
    (unbox_expr' unbox_underef_expr >> underef_expr' unbox_underef_expr) e

  (* extracts a `param` out of a `generic_param` if it's a const
     generic, otherwise returns `None`` *)
  let param_of_generic_const_param (g : generic_param) : param option =
    let* typ = match g.kind with GPConst { typ } -> Some typ | _ -> None in
    let ({ span; ident = var; _ } : generic_param) = g in
    let pat =
      let mode, mut, subpat = (ByValue, Immutable, None) in
      { p = PBinding { mut; mode; var; typ; subpat }; span; typ }
    in
    Some { pat; typ; typ_span = Some span; attrs = [] }

  let kind_of_item (item : item) : item_kind =
    match item.v with
    | Fn _ -> `Fn
    | TyAlias _ -> `TyAlias
    | Type _ -> `Type
    | IMacroInvokation _ -> `IMacroInvokation
    | Trait _ -> `Trait
    | Impl _ -> `Impl
    | Alias _ -> `Alias
    | Use _ -> `Use
    | Quote _ -> `Quote
    | HaxError _ -> `HaxError
    | NotImplementedYet -> `NotImplementedYet

  let rec expr_of_lhs (span : span) (lhs : lhs) : expr =
    match lhs with
    | LhsLocalVar { var; typ } -> { e = LocalVar var; typ; span }
    | LhsFieldAccessor { e; typ; field; _ } ->
        let e = expr_of_lhs span e in
        let f = { e = GlobalVar field; typ = TArrow ([ e.typ ], typ); span } in
        {
          e =
            App
              {
                f;
                args = [ e ];
                generic_args = [];
                bounds_impls = [];
                trait = None (* TODO: see issue #328 *);
              };
          typ;
          span;
        }
    | LhsArrayAccessor { e; typ; index; _ } ->
        let args = [ expr_of_lhs span e; index ] in
        call Core__ops__index__Index__index args span typ
    | LhsArbitraryExpr { e; _ } -> e

  (* module Box = struct *)
  (*   module Ty = struct *)
  (*     let destruct (t : ty) : ty option = *)
  (*       match t with *)
  (*       | TApp { ident = `Concrete box; args = [ GType sub; _alloc ] } *)
  (*         when Concrete_ident.eq_name Alloc__boxed__Box box -> *)
  (*           Some sub *)
  (*       | _ -> None *)

  (*     let alloc_ty = *)
  (*       TApp *)
  (*         { *)
  (*           ident = `Concrete (Concrete_ident.of_name Type Alloc__alloc__Global); *)
  (*           args = []; *)
  (*         } *)

  (*     let make (t : ty) : ty = *)
  (*       let ident = `Concrete (Concrete_ident.of_name Type Alloc__boxed__Box) in *)
  (*       TApp { ident; args = [ GType t; GType alloc_ty ] } *)
  (*   end *)

  (*   module Expr = struct *)
  (*     let destruct (e : expr) : expr option = *)
  (*       match e.e with *)
  (*       | App { f = { e = GlobalVar (`Primitive Box); _ }; args = [ arg ] } -> *)
  (*           Some arg *)
  (*       | _ -> None *)

  (*     let make (e : expr) : expr = *)
  (*       let boxed_ty = Ty.make e.typ in *)
  (*       let f_ty = TArrow ([ e.typ ], boxed_ty) in *)
  (*       let f = { e with typ = f_ty; e = GlobalVar (`Primitive Box) } in *)
  (*       { e with typ = boxed_ty; e = App { f; args = [ e ] } } *)
  (*   end *)
  (* end *)

  let rec collect_let_bindings' (e : expr) : (pat * expr * ty) list * expr =
    match e.e with
    | Let { monadic = _; lhs; rhs; body } ->
        let bindings, body = collect_let_bindings' body in
        ((lhs, rhs, e.typ) :: bindings, body)
    | _ -> ([], e)

  let collect_let_bindings (e : expr) : (pat * expr) list * expr =
    let bindings, body = collect_let_bindings' e in
    let types = List.map ~f:thd3 bindings in
    assert (
      match (List.drop_last types, types) with
      | Some init, _ :: tl ->
          List.zip_exn init tl |> List.for_all ~f:(uncurry [%eq: ty])
      | _ -> true);
    (* TODO: injecting the type of the lets in the body is bad.
       We should stay closer to Rust's inference.
       Here, we lose a bit of information.
    *)
    let body =
      { body with typ = List.hd types |> Option.value ~default:body.typ }
    in
    (List.map ~f:(fun (p, e, _) -> (p, e)) bindings, body)

  let rec map_body_of_nested_lets (f : expr -> expr) (e : expr) : expr =
    match e.e with
    | Let { monadic; lhs; rhs; body } ->
        {
          e with
          e = Let { monadic; lhs; rhs; body = map_body_of_nested_lets f body };
        }
    | _ -> f e

  let tuple_projector span (tuple_typ : ty) (len : int) (nth : int)
      (type_at_nth : ty) : expr =
    {
      span;
      (* TODO: require a span here *)
      typ = TArrow ([ tuple_typ ], type_at_nth);
      e = GlobalVar (`Projector (`TupleField (nth, len)));
    }

  let project_tuple (tuple : expr) (len : int) (nth : int) (type_at_nth : ty) :
      expr =
    {
      span = tuple.span;
      typ = type_at_nth;
      e =
        App
          {
            f = tuple_projector tuple.span tuple.typ len nth type_at_nth;
            args = [ tuple ];
            generic_args = [] (* TODO: see issue #328 *);
            bounds_impls = [];
            trait = None (* TODO: see issue #328 *);
          };
    }

  (** Concatenates the generics [g1] and [g2], making sure lifetimes appear first *)
  let concat_generics (g1 : generics) (g2 : generics) : generics =
    let params = g1.params @ g2.params in
    let constraints = g1.constraints @ g2.constraints in
    let lifetimes, others =
      List.partition_tf ~f:(fun p -> [%matches? GPLifetime _] p.kind) params
    in
    let params = lifetimes @ others in
    { params; constraints }

  module Place = struct
    type t = { place : place'; span : span; typ : ty }

    and place' =
      | LocalVar of Local_ident.t
      | Deref of expr
      | IndexProjection of { place : t; index : expr }
      | FieldProjection of { place : t; projector : global_ident }
    [@@deriving show]

    let deref_mut_allowed (t : ty) : bool =
      match t with
      | TApp { ident; _ } -> Global_ident.eq_name Alloc__vec__Vec ident
      | _ -> false

    let rec of_expr (e : expr) : t option =
      let wrap place = Some { place; span = e.span; typ = e.typ } in
      match e.e with
      | App { f = { e = GlobalVar (`Primitive Deref); _ }; args = [ e ]; _ }
        -> (
          match of_expr e with
          | Some { place = IndexProjection _; _ } as value -> value
          | _ -> wrap @@ Deref e)
      | LocalVar i -> wrap @@ LocalVar i
      | App
          {
            f = { e = GlobalVar (`Projector _ as projector); _ };
            args = [ place ];
            generic_args = _;
            bounds_impls = _;
            trait = _;
          (* TODO: see issue #328 *)
          } ->
          let* place = of_expr place in
          wrap @@ FieldProjection { place; projector }
      | App
          {
            f = { e = GlobalVar f; _ };
            args = [ place; index ];
            generic_args = _;
            bounds_impls = _;
            trait = _;
          (* TODO: see issue #328 *)
          }
        when Global_ident.eq_name Core__ops__index__Index__index f ->
          let* place = of_expr place in
          let place = IndexProjection { place; index } in
          Some { place; span = e.span; typ = e.typ }
      | App
          {
            f = { e = GlobalVar f; _ };
            args = [ place; index ];
            generic_args = _;
            bounds_impls = _;
            trait = _;
          (* TODO: see issue #328 *)
          }
        when Global_ident.eq_name Core__ops__index__IndexMut__index_mut f ->
          (* Note that here, we allow any type to be `index_mut`ed:
             Hax translates that to `Rust_primitives.Hax.update_at`.
             This will typecheck IFF there is an implementation.
          *)
          let* typ = Expect.mut_ref e.typ in
          let* place = Expect.mut_borrow place in
          let* place = of_expr place in
          let place = IndexProjection { place; index } in
          Some { place; span = e.span; typ }
      | _ -> None

    let rec to_expr (p : t) : expr =
      match p.place with
      | LocalVar v ->
          let e : expr' = LocalVar v in
          { e; typ = p.typ; span = p.span }
      | Deref e -> call' (`Primitive Deref) [ e ] p.span p.typ
      | FieldProjection { place; projector } ->
          let e = to_expr place in
          call' projector [ e ] p.span p.typ
      | IndexProjection { place; index } ->
          let e = to_expr place in
          call Core__ops__index__Index__index [ e; index ] p.span p.typ

    let expect_deref_mut (p : t) : t option =
      match p.place with
      | Deref e ->
          let* e = Expect.deref_mut_app e in
          let* e = Expect.mut_borrow e in
          of_expr e
      | _ -> None

    let expect_allowed_deref_mut (p : t) : t option =
      let* p = expect_deref_mut p in
      if deref_mut_allowed p.typ then Some p else None

    let skip_allowed_deref_mut (p : t) : t =
      Option.value ~default:p (expect_deref_mut p)
  end

  module StringList = struct
    module U = struct
      module T = struct
        type t = string * string list
        [@@deriving show, yojson, compare, sexp, eq, hash]
      end

      include T
      module C = Base.Comparator.Make (T)
      include C
    end

    include U
    module Map = Map.M (U)
  end
end

module MakeWithNamePolicy (F : Features.T) (NP : Concrete_ident.NAME_POLICY) =
struct
  include Make (F)
  open AST
  module Concrete_ident_view = Concrete_ident.MakeViewAPI (NP)

  let group_items_by_namespace (items : item list) : item list StringList.Map.t
      =
    let h = Hashtbl.create (module StringList) in
    List.iter items ~f:(fun item ->
        let ns = Concrete_ident_view.to_namespace item.ident in
        let items = Hashtbl.find_or_add h ns ~default:(fun _ -> ref []) in
        items := !items @ [ item ]);
    Map.of_iteri_exn
      (module StringList)
      ~iteri:(Hashtbl.map h ~f:( ! ) |> Hashtbl.iteri)
end

module ASTGenerator = struct
  module AST = Ast.Make (Features.Full)
  open AST

  type ast_type =
    | CONCRETE_IDENT
    | LITERAL
    | TY
    | EXPR
    | GENERICS
    | GLOBAL_IDENT
    | PAT
    | LOCAL_IDENT
    | IMPL_EXPR
    | ITEM

  let rec generate_helper (t : ast_type) (indexes : int list) : Yojson.Safe.t * int list =
    let i, indexes = List.hd_exn indexes, Option.value ~default:[] (List.tl indexes) in
    let cases: (unit -> Yojson.Safe.t * int list) list =
      (match t with
       | CONCRETE_IDENT ->
         [
           (fun () -> ([%yojson_of: concrete_ident] (Concrete_ident.of_name Value Hax_lib__RefineAs__into_checked), indexes))
         ]

       | LITERAL ->
         [
           (fun () -> ([%yojson_of: literal] (String "dummy"), indexes));
           (fun () -> ([%yojson_of: literal] (Char 'a'), indexes));
           (fun () -> ([%yojson_of: literal] (Int {value = "dummy"; negative = false; kind = { size = S8; signedness = Unsigned }}), indexes));
           (fun () -> ([%yojson_of: literal] (Float {value = "dummy"; negative = false; kind = F16}), indexes));
           (fun () -> ([%yojson_of: literal] (Bool false), indexes));
         ]

       | TY ->
         [
           (fun () -> ([%yojson_of: ty] TBool, indexes));
           (fun () -> ([%yojson_of: ty] TChar, indexes));
           (fun () -> ([%yojson_of: ty] (TInt { size = S8 ; signedness = Unsigned}), indexes));
           (fun () -> ([%yojson_of: ty] (TFloat F16), indexes));
           (fun () -> ([%yojson_of: ty] TStr, indexes));
           (fun () ->
              let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
              let g_ident = [%of_yojson: global_ident] g_ident in
              ([%yojson_of: ty] (TApp { ident = g_ident ; args = [] }), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              let length, indexes = generate_helper EXPR indexes in (* Should be const expr ! *)
              let length = [%of_yojson: expr] length in
              ([%yojson_of: ty] (TArray {typ; length;}), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              ([%yojson_of: ty] (TSlice {witness = Features.On.slice; ty = typ;}), indexes));
           (fun () ->
              ([%yojson_of: ty] (TRawPointer {witness = Features.On.raw_pointer;}), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              ([%yojson_of: ty] (TRef {
                   witness = Features.On.reference;
                   region = "todo";
                   typ = typ;
                   mut = Immutable;
                 }), indexes));
           (fun () ->
              let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
              let l_ident = [%of_yojson : local_ident] l_ident in
              ([%yojson_of: ty] (TParam l_ident), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson : ty] typ in
              ([%yojson_of: ty] (TArrow ([] ,typ)), indexes));
           (fun () ->
              let impl_expr, indexes = generate_helper IMPL_EXPR indexes in
              let impl_expr = [%of_yojson: impl_expr] impl_expr in

              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              let c_ident = [%of_yojson: concrete_ident] c_ident in
              ([%yojson_of: ty] (TAssociatedType {impl = impl_expr; item = c_ident}), indexes));
           (fun () ->
              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              let c_ident = [%of_yojson: concrete_ident] c_ident in
              ([%yojson_of: ty] (TOpaque c_ident), indexes));
           (fun () ->
              ([%yojson_of: ty] (TDyn { witness = Features.On.dyn; goals= []}), indexes));
         ]

       | EXPR ->
         let expr_shell e indexes =
           let typ, indexes = generate_helper TY indexes in
           (`Assoc [
               ("e" , e ) ;
               ("span" , `Assoc [("id" , `Int 79902) ; ("data" , `List [])]) ;
               ("typ" , typ)
             ], indexes)
         in
         List.map ~f:(fun expr_f -> (fun () ->
             let (expr', indexes) = expr_f () in
             expr_shell expr' indexes))
           [
             (fun () ->
                let cond, indexes = generate_helper EXPR indexes in
                let cond = [%of_yojson: expr] cond in

                let then_, indexes = generate_helper EXPR indexes in
                let then_ = [%of_yojson: expr] then_ in

                ([%yojson_of: expr'] (If {
                     cond = cond;
                     then_ = then_;
                     else_ = None
                   }), indexes));
             (fun () ->
                let f, indexes = generate_helper EXPR indexes in
                let f = [%of_yojson: expr] f in

                let args, indexes = generate_helper EXPR indexes in
                let args = [%of_yojson: expr] args in

                ([%yojson_of: expr'] (App { f; args = [ args (* must have 1+ items *) ]; generic_args = []; bounds_impls = []; trait = None; }), indexes));
             (fun () ->
                let lit, indexes = generate_helper LITERAL indexes in
                let lit = [%of_yojson: literal] lit in
                ([%yojson_of: expr'] (Literal lit), indexes));
             (fun () -> ([%yojson_of: expr'] (Array []), indexes));
             (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson: global_ident] g_ident in

                ([%yojson_of: expr'] (Construct {
                     constructor = g_ident;
                     is_record = false;
                     is_struct = false;
                     fields = [];
                     base = None;
                   }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                ([%yojson_of: expr'] (Match { scrutinee = expr; arms = [] }), indexes));
             (fun () ->
                let lhs, indexes = generate_helper PAT indexes in
                let lhs = [%of_yojson: pat] lhs in

                let rhs, indexes = generate_helper EXPR indexes in
                let rhs = [%of_yojson: expr] rhs in

                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in

                ([%yojson_of: expr'] (Let { monadic = None; lhs; rhs; body; }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                ([%yojson_of: expr'] (Block { e = expr; safety_mode = Safe; witness = Features.On.block }), indexes));
             (fun () ->
                let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
                let l_ident = [%of_yojson : local_ident] l_ident in
                ([%yojson_of: expr'] (LocalVar l_ident), indexes));
             (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson : global_ident] g_ident in
                ([%yojson_of: expr'] (GlobalVar g_ident), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ([%yojson_of: expr'] (Ascription { e = expr; typ; }), indexes));
             (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson : global_ident] g_ident in
                ([%yojson_of: expr'] (MacroInvokation {
                  macro = g_ident;
                  args = "dummy";
                  witness = Features.On.macro;
                }), indexes));
             (fun () ->
                let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
                let l_ident = [%of_yojson : local_ident] l_ident in

                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ([%yojson_of: expr'] (Assign {
                     lhs = LhsLocalVar { var = l_ident; typ; };
                     e = expr;
                     witness = Features.On.mutable_variable;
                   }), indexes));
             (fun () ->
                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in

                ([%yojson_of: expr'] (Loop {
                 body = body;
                 kind = UnconditionalLoop;
                 state = None;
                 control_flow = None;
                 label = None;
                 witness = Features.On.loop;
               }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (Break {
                     e = expr;
                     acc = None;
                     label = None;
                     witness = (Features.On.break, Features.On.loop);
               }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (Return { e = expr; witness = Features.On.early_exit }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ([%yojson_of: expr'] (QuestionMark {
                     e = expr;
                     return_typ = typ;
                     witness = Features.On.question_mark;
                   }), indexes));
             (fun () -> ([%yojson_of: expr'] (Continue {
                  acc = None;
                  label = None;
                  witness = (Features.On.continue, Features.On.loop);
                }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (Borrow {
                  kind = Shared;
                  e = expr;
                  witness = Features.On.reference
                }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (AddressOf
               { mut = Immutable; e = expr; witness = Features.On.raw_pointer }), indexes));
             (fun () ->
                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in
                ([%yojson_of: expr'] (Closure { params = []; body; captures = [] }), indexes));
             (* TODO: The two remaing ast elements! *)
             (* EffectAction *)
             (*   { action = Features.On.monadic_action; argument = dummy_expr }; *)
             (* Quote { contents = []; witness = Features.On.quote }; *)
           ]

       | GENERICS ->
         [
           (fun () -> ([%yojson_of: generics] { params = []; constraints = [] }, indexes));
         ]

       | GLOBAL_IDENT ->
         [fun () ->
            let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
            (`List [ `String "Concrete" ; c_ident ], indexes)
         ]

       | PAT ->

         let pat_shell v indexes =
           let typ, indexes = generate_helper TY indexes in
           (`Assoc [
               ("p" , v ) ;
               ("span" , `Assoc [("id" , `Int 79902) ; ("data" , `List [])]) ;
               ("typ" , typ) ;
             ], indexes)
         in
         List.map ~f:(fun pat_f -> (fun () ->
             let (pat', indexes) = pat_f () in
             pat_shell pat' indexes))
         [
           (fun () -> ([%yojson_of: pat'] PWild, indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in

              let pat, indexes = generate_helper PAT indexes in
              let pat = [%of_yojson: pat] pat in
              ([%yojson_of: pat'] (PAscription {
                   typ;
                   typ_span = Span.dummy ();
                   pat;
                 }), indexes));
           (fun () ->
              let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
              let g_ident = [%of_yojson: global_ident] g_ident in
              ([%yojson_of: pat'] (PConstruct
             {
               constructor = g_ident;
               is_record = false;
               is_struct = false;
               fields = [];
             }), indexes));
           (fun () ->
              let lhs_pat, indexes = generate_helper PAT indexes in
              let lhs_pat = [%of_yojson: pat] lhs_pat in

              let rhs_pat, indexes = generate_helper PAT indexes in
              let rhs_pat = [%of_yojson: pat] rhs_pat in
              ([%yojson_of: pat'] (POr {
                   subpats = [ lhs_pat; rhs_pat ]
                 }), indexes));
           (fun () -> ([%yojson_of: pat'] (PArray { args = [] }), indexes));
           (fun () ->
              let pat, indexes = generate_helper PAT indexes in
              let pat = [%of_yojson: pat] pat in
              ([%yojson_of: pat'] (PDeref {
                   subpat = pat;
                   witness = Features.On.reference
                 }), indexes));
           (fun () ->
              let lit, indexes = generate_helper LITERAL indexes in
              let lit = [%of_yojson: literal] lit in
              ([%yojson_of: pat'] (PConstant { lit }), indexes));
           (fun () ->
              let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
              let l_ident = [%of_yojson: local_ident] l_ident in

              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              ([%yojson_of: pat'] (PBinding
             {
               mut = Mutable Features.On.mutable_variable;
               mode = ByValue;
               var = l_ident;
               typ;
               subpat = None;
             }), indexes));
         ]

       | LOCAL_IDENT ->
         [fun () ->
            (`Assoc [("name" , `String "dummy") ; ("id" , `List [`List [`String "Typ"] ; `Int 0])], indexes)
         ]

       | IMPL_EXPR ->
         [fun () ->
            let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
            (`Assoc [
                ("kind" , `List [`String "Self"]) ;
                ("goal" , `Assoc [
                    ("trait" , c_ident) ;
                    ("args" , `List [])])
              ], indexes)
         ]

       | ITEM ->
         let item_shell v indexes =
           let ident, indexes = generate_helper CONCRETE_IDENT indexes in
           (`Assoc [
               ("v" , v ) ;
               ("span" , `Assoc [("id" , `Int 79902) ; ("data" , `List [])]) ;
               ("ident" , ident) ;
               ("attrs" , `List [])
             ], indexes)
         in
         List.map ~f:(fun item_f -> (fun () ->
             let (item', indexes) = item_f () in
             item_shell item' indexes))
           [
             (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in

                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in
                ([%yojson_of: item'] (Fn {name; generics; body; params = []; safety = Safe}), indexes));
            (fun () ->
               let name, indexes = generate_helper CONCRETE_IDENT indexes in
               let name = [%of_yojson: concrete_ident] name in

               let generics, indexes = generate_helper GENERICS indexes in
               let generics = [%of_yojson: generics] generics in

               let typ, indexes = generate_helper TY indexes in
               let typ = [%of_yojson: ty] typ in
               ([%yojson_of: item'] (TyAlias {name; generics; ty = typ;}), indexes));
            (* enum *)
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in
              ([%yojson_of: item'] (Type {name; generics; variants = []; is_struct = false}), indexes));
            (* struct *)
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in
              ([%yojson_of: item'] (Type {name; generics; variants = []; is_struct = true}), indexes));
            (fun () ->
               let macro, indexes = generate_helper CONCRETE_IDENT indexes in
               let macro = [%of_yojson: concrete_ident] macro in
               ([%yojson_of: item'] (IMacroInvokation {macro; argument = "TODO"; span = Span.dummy(); witness = Features.On.macro}), indexes));
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in
              ([%yojson_of: item'] (Trait {
                   name ;
                   generics ;
                   items = [];
                   safety = Safe;
                 }), indexes));
            (fun () ->
              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in

              let ty, indexes = generate_helper TY indexes in
              let ty = [%of_yojson: ty] ty in

              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              let c_ident = [%of_yojson: concrete_ident] c_ident in
              ([%yojson_of: item'] (Impl {
                   generics;
                   self_ty = ty;
                   of_trait = (c_ident, []) ;
                   items = [] ;
                   parent_bounds = [] ;
                   safety = Safe
                 }), indexes));
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let item, indexes = generate_helper CONCRETE_IDENT indexes in
              let item = [%of_yojson: concrete_ident] item in
               ([%yojson_of: item'] (Alias { name;  item }), indexes));
            (fun () ->
              ([%yojson_of: item'] (Use {
                  path = [];
                  is_external = false;
                  rename = None
                }), indexes));
            (* Quote { contents = []; witness = Features.On.quote }; *)
            (* HaxError "dummy"; *)
            (* NotImplementedYet; *)
           ]
      )  in
    List.nth_exn cases i ()

  let generate (t : ast_type) (indexes : int list) : Yojson.Safe.t =
    fst (generate_helper t indexes)

  (* AST depth:
     0 is constants (no recursion),
     1 is the flat AST with each AST elements present,
     inf is all possible expressions *)
  let rec generate_depth depth (pre : int list) (t : ast_type) : (int list) list =
    List.map ~f:(fun l -> pre @ l)
      (match t with
       (* TODO: Base dummy values *)
       | CONCRETE_IDENT -> [[0]]
       | GLOBAL_IDENT -> generate_depth_list_helper depth [0] [CONCRETE_IDENT]
       | LOCAL_IDENT -> [[0]]
       | IMPL_EXPR -> [[0;0]]
       | GENERICS -> [[0]]

       (* Fully defined AST elements *)
       | LITERAL ->
         [
           (* String *)
           [0];
           (* Char *)
           [1];
           (* Int *)
           [2];
           (* Float *)
           [3];
           (* Bool *)
           [4]
         ]
       | TY ->
         [
           (* TBool *)
           [0];
           (* TChar *)
           [1];
           (* TInt *)
           [2];
           (* TFloat *)
           [3];
           (* TStr *)
           [4];
         ] @
         (* TApp *)
         generate_depth_list_helper depth [5] [GLOBAL_IDENT] (* TODO: Any number of extra ty args? *)
         @
         (* TArray *)
         generate_depth_list_helper (depth-1) [6] [TY; EXPR]
         @
         (* TSlice *)
         generate_depth_list_helper (depth-1) [7] [TY]
         @
         [
           (* TRawPointer *)
           [8]
         ]
         @
         (* TRef *)
         generate_depth_list_helper (depth-1) [9] [TY]
         @
         (* TParam *)
         generate_depth_list_helper depth [10] [LOCAL_IDENT]
         @
         (* TArrow *)
         generate_depth_list_helper (depth-1) [11] [TY]
         @
         (* TAssociatedType *)
         generate_depth_list_helper (depth-1) [12] [IMPL_EXPR; CONCRETE_IDENT ]
         @
         (* TOpaque *)
         generate_depth_list_helper (depth-1) [13] [CONCRETE_IDENT]
         @
         [
           (* TDyn *)
           [14]
         ]
       | PAT ->
         List.map ~f:(fun x -> x @ [0] (* TODO: Append correct type, instead of dummy / guessing *)) (
           [
             (* PWild *)
             [0];
           ]
           @
           (* PAscription *)
           generate_depth_list_helper (depth-1) [1] [TY; PAT]
           @
           (* PConstruct *)
           generate_depth_list_helper depth [2] [GLOBAL_IDENT]
           @
           (* POr *)
           generate_depth_list_helper (depth-1) [3] [PAT; PAT]
           @
           [
             (* PArray *)
             [4];
           ]
           @
           (* PDeref *)
           generate_depth_list_helper (depth-1) [5] [PAT]
           @
           (* PConstant *)
           generate_depth_list_helper depth [6] [LITERAL]
           @
           (* PBinding *)
           generate_depth_list_helper (depth-1) [7] [LOCAL_IDENT; TY]
         )
       | EXPR ->
         List.map ~f:(fun x -> x @ [0] (* TODO: Append correct type, instead of dummy / guessing *))
           (
             (* If *)
             generate_depth_list_helper (depth-1) [0] [EXPR; EXPR] (*; expr3 *)
             @
             (* App *)
             generate_depth_list_helper (depth-1) [1] [EXPR; EXPR]
             @
             (* Literal *)
             generate_depth_list_helper depth [2] [LITERAL]
             @
             [
               (* Array *)
               [3];
             ]
             @
             (* Construct *)
             generate_depth_list_helper (depth-1) [4] [GLOBAL_IDENT]
             @
             (* Match *)
             generate_depth_list_helper (depth-1) [5] [EXPR]
             @
             (* Let *)
             generate_depth_list_helper (depth-1) [6] [PAT; EXPR; EXPR]
             @
             (* Block *)
             generate_depth_list_helper (depth-1) [7] [EXPR]
             @
             (* LocalVar *)
             generate_depth_list_helper (depth-1) [8] [LOCAL_IDENT]
             @
             (* GlobalVar *)
             generate_depth_list_helper (depth-1) [9] [GLOBAL_IDENT]
             @
             (* Ascription *)
             generate_depth_list_helper (depth-1) [10] [EXPR; TY]
             @
             (* MacroInvokation *)
             generate_depth_list_helper (depth-1) [11] [GLOBAL_IDENT]
             @
             (* Assign *)
             generate_depth_list_helper (depth-1) [12] [LOCAL_IDENT; EXPR; TY]
             @
             (* Loop *)
             generate_depth_list_helper (depth-1) [13] [EXPR]
             @
             (* Break *)
             generate_depth_list_helper (depth-1) [14] [EXPR]
             @
             (* Return *)
             generate_depth_list_helper (depth-1) [15] [EXPR]
             @
             (* QuestionMark *)
             generate_depth_list_helper (depth-1) [16] [EXPR; TY]
             @
             [
               (* Continue *)
               [17];
             ]
             @
             (* Borrow *)
             generate_depth_list_helper (depth-1) [18] [EXPR]
             @
             (* AddressOf *)
             generate_depth_list_helper (depth-1) [19] [EXPR]
             @
             (* Closure *)
             generate_depth_list_helper (depth-1) [20] [EXPR]
           )
       | ITEM ->
         List.concat_map ~f:(fun x -> generate_depth_list_helper depth x [CONCRETE_IDENT]) (
           (* Fn *)
           generate_depth_list_helper (depth-1) [0] [CONCRETE_IDENT; GENERICS; EXPR]
           @
           (* TYAlias *)
           generate_depth_list_helper (depth-1) [1] [CONCRETE_IDENT; GENERICS; TY]
           @
           (* TYpe *)
           generate_depth_list_helper (depth-1) [2] [CONCRETE_IDENT; GENERICS]
           @
           (* TYpe *)
           generate_depth_list_helper (depth-1) [3] [CONCRETE_IDENT; GENERICS]
           @
           (* IMacroInvokation *)
           generate_depth_list_helper depth [4] [CONCRETE_IDENT]
           @
           (* Trait *)
           generate_depth_list_helper (depth-1) [5] [CONCRETE_IDENT; GENERICS]
           @
           (* Impl *)
           generate_depth_list_helper (depth-1) [6] [GENERICS; TY; CONCRETE_IDENT]
           @
           (* Alias *)
           generate_depth_list_helper (depth-1) [7] [CONCRETE_IDENT; CONCRETE_IDENT]
           @
           [
             (* Use *)
             [8];
           ]
         )
      )
  and generate_depth_list depth (pre : int list) (t : ast_type list) : (int list) list =
    match t with
    | [] -> []
    | [x] -> generate_depth depth pre x
    | (x :: xs) ->
      List.concat_map ~f:(fun pre -> generate_depth_list depth pre xs) (generate_depth depth pre x)
  and generate_depth_list_helper depth (pre : int list) (t : ast_type list) : (int list) list =
    if depth >= 0
    then generate_depth_list depth pre t
    else []

  let rec flatten (l : (int list) list) : (int list) list =
    match l with
    | ((x :: xs) :: (y :: ys) :: ls) ->
      (if phys_equal x y then [] else [(x :: xs)]) @ flatten ((y :: ys) :: ls)
    | _ -> l

  let generate_literals =
    let literal_args = flatten (generate_depth 0 [] LITERAL) in
    List.map ~f:(fun x -> [%of_yojson: literal] (generate LITERAL x)) literal_args

  let generate_tys : ty list =
    let ty_args = flatten (generate_depth 1 [] TY) in
    List.map ~f:(fun x -> [%of_yojson: ty] (generate TY x)) ty_args

  let generate_pats =
    let pat_args = flatten (generate_depth 1 [] PAT) in
    List.map ~f:(fun x -> [%of_yojson: pat] (generate PAT x)) pat_args

  let generate_expr =
    let expr_args = flatten (generate_depth 1 [] EXPR) in
    List.map ~f:(fun x -> [%of_yojson: expr] (generate EXPR x)) expr_args

  let generate_items =
    let item_args = flatten (generate_depth 1 [] ITEM) in
    List.map ~f:(fun x -> [%of_yojson: item] (generate ITEM x)) item_args

  let generate_full_ast : (literal list * ty list * pat list * expr list * item list) =
    (** Can use rendering tools for EBNF e.g. https://rr.red-dove.com/ui **)
    (** bfs with no recursion, elements seen before are replaced with 0 depth (constant) elements **)

    let my_literals = generate_literals in
    let my_tys   = generate_tys in
    let my_pats  = generate_pats in
    let my_exprs = generate_expr in
    let my_items = generate_items in
    (my_literals, my_tys, my_pats, my_exprs, my_items)
end
