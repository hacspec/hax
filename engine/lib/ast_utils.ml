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

  module Expect = struct
    let mut_borrow (e : expr) : expr option =
      match e.e with Borrow { kind = Mut _; e; _ } -> Some e | _ -> None

    let deref (e : expr) : expr option =
      match e.e with
      | App { f = { e = GlobalVar (`Primitive Deref); _ }; args = [ e ]; _ } ->
          Some e
      | _ -> None

    let concrete_app1 (f : Concrete_ident.name) (e : expr) : expr option =
      match e.e with
      | App
          {
            f = { e = GlobalVar (`Concrete f'); _ };
            args = [ e ];
            generic_args = _;
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
          inherit ['s] VisitorsRuntime.monoid
          method private zero = Set.empty (module Global_ident)
          method private plus = Set.union
        end
    end

    module Concrete_ident = struct
      include Set.M (Concrete_ident)

      class ['s] monoid =
        object
          inherit ['s] VisitorsRuntime.monoid
          method private zero = Set.empty (module Concrete_ident)
          method private plus = Set.union
        end
    end

    module Local_ident = struct
      include Set.M (Local_ident)

      class ['s] monoid =
        object
          inherit ['s] VisitorsRuntime.monoid
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
          inherit ['s] VisitorsRuntime.monoid
          method private zero = Set.empty (module TypedLocalIdent)
          method private plus = Set.union
        end
    end
  end

  module Mappers = struct
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

    (** Add type ascription nodes in nested function calls.  This helps
    type inference in the presence of associated types in backends
    that don't support them well (F* for instance). *)
    let add_typ_ascription =
      let is_app = Expect.concrete_app' >> Option.is_some in
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
                } ->
                ascribe
                  { e with e = App { f; args = [ ascribe arg ]; generic_args } }
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
        (fv_of_arbitrary_lhs :
          F.arbitrary_lhs -> expr -> Sets.TypedLocalIdent.t) =
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

  (** Produces a local identifier which is locally fresh **with respect
      to expressions {exprs}**. *)
  let fresh_local_ident_in_expr (exprs : expr list) (prefix : string) :
      Local_ident.t =
    let free_suffix =
      List.map ~f:(Reducers.collect_local_idents#visit_expr ()) exprs
      |> Set.union_list (module Local_ident)
      |> Set.to_list
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
    | PConstruct { name = `TupleType 1; args = [ { pat; _ } ]; _ } ->
        remove_tuple1_pat pat
    | _ -> p

  let rec remove_tuple1 (t : ty) : ty =
    match t with
    | TApp { ident = `TupleType 1; args = [ GType t ] } -> remove_tuple1 t
    | _ -> t

  let remove_unsize (e : expr) : expr =
    match e.e with
    | App { f = { e = GlobalVar f; _ }; args = [ e ]; generic_args = _ }
      when Global_ident.eq_name Rust_primitives__unsize f ->
        e
    | _ -> e

  (* let rec remove_empty_tap *)

  let is_unit_typ : ty -> bool =
    remove_tuple1 >> [%matches? TApp { ident = `TupleType 0; _ }]

  let rec pat_is_expr (p : pat) (e : expr) =
    match (p.p, e.e) with
    | _, Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; _ } ->
        pat_is_expr p e
    | PBinding { subpat = None; var = pv; _ }, LocalVar ev ->
        [%eq: local_ident] pv ev
    | ( PConstruct { name = pn; args = pargs; _ },
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

  let make_var_pat (var : local_ident) (typ : ty) (span : span) : pat =
    {
      p = PBinding { mut = Immutable; mode = ByValue; var; typ; subpat = None };
      span;
      typ;
    }

  let ty_equality (a : ty) (b : ty) : bool =
    let replace_spans =
      object
        inherit [_] item_map
        method visit_t () x = x
        method visit_mutability _ () m = m
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

  let make_wild_pat (typ : ty) (span : span) : pat = { p = PWild; span; typ }

  let make_unit_param (span : span) : param =
    let typ = unit_typ in
    let pat = make_wild_pat typ span in
    { pat; typ; typ_span = None; attrs = [] }

  let make_seq (e1 : expr) (e2 : expr) : expr =
    make_let (make_wild_pat e1.typ e1.span) e1 e2

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
                name = `TupleCons len;
                args = tuple;
                is_record = false;
                is_struct = true;
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

  let call' f (args : expr list) span ret_typ =
    let typ = TArrow (List.map ~f:(fun arg -> arg.typ) args, ret_typ) in
    let e = GlobalVar f in
    {
      e =
        App
          {
            f = { e; typ; span };
            args;
            generic_args =
              []
              (* TODO: see issue #328, and check that for evrey call to `call'` *);
          };
      typ = ret_typ;
      span;
    }

  let call ?(kind : Concrete_ident.Kind.t = Value)
      (f_name : Concrete_ident.name) (args : expr list) span ret_typ =
    call' (`Concrete (Concrete_ident.of_name kind f_name)) args span ret_typ

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
    let item : AST.item -> Ast.Full.item = Stdlib.Obj.magic
  end

  let unbox_expr' (next : expr -> expr) (e : expr) : expr =
    match e.e with
    | App { f = { e = GlobalVar f; _ }; args = [ e ]; generic_args = _ }
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

  let rec expr_of_lhs (span : span) (lhs : lhs) : expr =
    match lhs with
    | LhsLocalVar { var; typ } -> { e = LocalVar var; typ; span }
    | LhsFieldAccessor { e; typ; field; _ } ->
        let e = expr_of_lhs span e in
        let f = { e = GlobalVar field; typ = TArrow ([ e.typ ], typ); span } in
        {
          e =
            App
              { f; args = [ e ]; generic_args = [] (* TODO: see issue #328 *) };
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
          };
    }

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
          (* TODO: see issue #328 *)
          } ->
          let* place = of_expr place in
          wrap @@ FieldProjection { place; projector }
      | App
          {
            f = { e = GlobalVar f; _ };
            args = [ place; index ];
            generic_args = _;
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
