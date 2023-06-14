open Base
open Utils
open Ast

type visit_level = ExprLevel | TypeLevel

module TypedLocalIdent (Ty : sig
  type ty [@@deriving show, yojson]
end) =
struct
  module T = struct
    type t = Ast.LocalIdent.t * Ty.ty [@@deriving show, yojson]

    let sexp_of_t : t -> _ = fst >> Ast.LocalIdent.sexp_of_t
    let compare (a : t) (b : t) = [%compare: Ast.LocalIdent.t] (fst a) (fst b)
    let equal (a : t) (b : t) = [%eq: Ast.LocalIdent.t] (fst a) (fst b)
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

  module Sets = struct
    module GlobalIdent = struct
      include Set.M (GlobalIdent)

      class ['s] monoid =
        object
          inherit ['s] VisitorsRuntime.monoid
          method private zero = Set.empty (module GlobalIdent)
          method private plus = Set.union
        end
    end

    module LocalIdent = struct
      include Set.M (LocalIdent)

      class ['s] monoid =
        object
          inherit ['s] VisitorsRuntime.monoid
          method private zero = Set.empty (module LocalIdent)
          method private plus = Set.union
        end
    end

    module TypedLocalIdent = struct
      include Set.M (TypedLocalIdent)

      let show (x : t) : string =
        [%show: TypedLocalIdent.t list] @@ Set.to_list x

      let pp (fmt : Caml.Format.formatter) (s : t) : unit =
        Caml.Format.pp_print_string fmt @@ show s

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

        method! visit_span s =
          function
          | Dummy _ -> Dummy { id = FreshSpanId.make () }
          | Span s -> Span { s with id = FreshSpanId.make () }
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
                } ->
                expr sub
            | _ -> super#visit_expr s e
          in
          expr e
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

    let rename_global_idents_item
        (f : visit_level -> global_ident -> global_ident) : item -> item =
      (rename_global_idents f)#visit_item ExprLevel
  end

  module Reducers = struct
    let collect_local_idents =
      object
        inherit [_] expr_reduce as _super
        inherit [_] Sets.LocalIdent.monoid as m
        method visit_t _ _ = m#zero
        method visit_mutability (_f : unit -> _ -> _) () _ = m#zero
        method! visit_local_ident _ x = Set.singleton (module LocalIdent) x
      end

    let collect_global_idents =
      object
        inherit ['self] expr_reduce as _super
        inherit [_] Sets.GlobalIdent.monoid as m
        method visit_t _ _ = m#zero
        method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

        method! visit_global_ident (_env : unit) (x : GlobalIdent.t) =
          Set.singleton (module GlobalIdent) x
      end

    let variables_of_pat (p : pat) : Sets.LocalIdent.t =
      (object
         inherit [_] expr_reduce as super
         inherit [_] Sets.LocalIdent.monoid as m
         method visit_t _ _ = m#zero
         method visit_mutability (_f : unit -> _ -> _) () _ = m#zero

         method! visit_PBinding env _ _ var _ subpat =
           m#plus
             (Set.singleton (module LocalIdent) var)
             (Option.value_map subpat ~default:m#zero
                ~f:(fst >> super#visit_pat env))
      end)
        #visit_pat
        () p

    let variables_of_pats : pat list -> Sets.LocalIdent.t =
      List.map ~f:variables_of_pat >> Set.union_list (module LocalIdent)

    let without_vars (mut_vars : Sets.TypedLocalIdent.t)
        (vars : Sets.LocalIdent.t) =
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
            | ForLoop { var = _not_mutable; _ } -> []
            | ForIndexLoop { var = _not_mutable; _ } -> [])
            @ (state
              |> Option.map ~f:(fun { bpat; _ } -> variables_of_pat bpat)
              |> Option.to_list)
            |> Set.union_list (module LocalIdent)
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
      LocalIdent.t =
    let free_suffix =
      List.map ~f:(Reducers.collect_local_idents#visit_expr ()) exprs
      |> Set.union_list (module LocalIdent)
      |> Set.to_list
      |> List.filter_map ~f:(fun ({ name; _ } : local_ident) ->
             String.chop_prefix ~prefix name)
      |> List.map ~f:(function "" -> "0" | s -> s)
      |> List.filter_map ~f:Caml.int_of_string_opt
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
        LocalIdent.var_id_of_int (-1);
    }

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

  let ty_equalily (a : ty) (b : ty) : bool =
    let replace_spans =
      object
        inherit [_] item_map
        method visit_t () x = x
        method visit_mutability _ () m = m
        method! visit_span s = function _ -> Dummy { id = 0 }
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
          p = PConstruct { name = `TupleCons len; args = tuple; record = false };
          typ = make_tuple_typ @@ List.map ~f:(fun { pat; _ } -> pat.typ) tuple;
          span;
        }

  let make_tuple_pat' (pats : pat list) : pat =
    let len = List.length pats in
    List.mapi ~f:(fun i pat -> { field = `TupleField (i, len); pat }) pats
    |> make_tuple_pat'' (union_spans @@ List.map ~f:(fun p -> p.span) pats)

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
            constructs_record = false;
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
  let call_Constructor (crate : string) (path_hd : string)
      (path_tl : string list) (args : expr list) span ret_typ =
    let path = Non_empty_list.(path_hd :: path_tl) in
    let typ = TArrow (List.map ~f:(fun arg -> arg.typ) args, ret_typ) in
    let mk_field =
      let len = List.length args in
      fun n -> `TupleField (len, n)
    in
    let fields = List.mapi ~f:(fun i arg -> (mk_field i, arg)) args in
    {
      e =
        Construct
          {
            constructor = `Concrete { crate; path };
            constructs_record = false;
            fields;
            base = None;
          };
      typ = ret_typ;
      span;
    }

  let call (crate : string) (path_hd : string) (path_tl : string list)
      (args : expr list) span ret_typ =
    let path = Non_empty_list.(path_hd :: path_tl) in
    let typ = TArrow (List.map ~f:(fun arg -> arg.typ) args, ret_typ) in
    let e = GlobalVar (`Concrete { crate; path }) in
    { e = App { f = { e; typ; span }; args }; typ = ret_typ; span }

  let string_lit span (s : string) : expr =
    { span; typ = TStr; e = Literal (String s) }

  let hax_failure_expr' span (typ : ty) (context, kind) (ast : string) =
    let error = Diagnostics.pretty_print_context_kind context kind in
    let args = List.map ~f:(string_lit span) [ error; ast ] in
    call "hax_error" "hax_failure" [] args span typ

  let hax_failure_expr span (typ : ty) (context, kind) (expr0 : Ast.Full.expr) =
    hax_failure_expr' span typ (context, kind) (Print_rust.pexpr_str expr0)

  let hax_failure_typ =
    let ident =
      `Concrete { crate = "hax_error"; path = Non_empty_list.[ "hax_failure" ] }
    in
    TApp { ident; args = [] }

  module LiftToFullAst = struct
    let expr : AST.expr -> Ast.Full.expr = Obj.magic
    let item : AST.expr -> Ast.Full.expr = Obj.magic
  end

  module Box = struct
    module Ty = struct
      let destruct (t : ty) : ty option =
        match t with
        | TApp
            {
              ident =
                `Concrete
                  { crate = "alloc"; path = Non_empty_list.[ "boxed"; "Box" ] };
              args = [ GType sub; _alloc ];
            } ->
            Some sub
        | _ -> None

      let alloc_ty =
        let path = Non_empty_list.[ "alloc"; "Global" ] in
        TApp { ident = `Concrete { crate = "alloc"; path }; args = [] }

      let make (t : ty) : ty =
        let ident =
          let path = Non_empty_list.[ "boxed"; "Box" ] in
          `Concrete { crate = "alloc"; path }
        in
        TApp { ident; args = [ GType t; GType alloc_ty ] }
    end

    module Expr = struct
      let destruct (e : expr) : expr option =
        match e.e with
        | App { f = { e = GlobalVar (`Primitive Box); _ }; args = [ arg ] } ->
            Some arg
        | _ -> None

      let make (e : expr) : expr =
        let boxed_ty = Ty.make e.typ in
        let f_ty = TArrow ([ e.typ ], boxed_ty) in
        let f = { e with typ = f_ty; e = GlobalVar (`Primitive Box) } in
        { e with typ = boxed_ty; e = App { f; args = [ e ] } }
    end
  end

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

  let tuple_projector (tuple_typ : ty) (len : int) (nth : int)
      (type_at_nth : ty) : expr =
    {
      span = Dummy { id = FreshSpanId.make () };
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
            f = tuple_projector tuple.typ len nth type_at_nth;
            args = [ tuple ];
          };
    }

  let group_items_by_namespace (items : item list) : item list Namespace.Map.t =
    let h = Hashtbl.create (module Namespace) in
    List.iter items ~f:(fun item ->
        let items =
          Hashtbl.find_or_add h item.parent_namespace ~default:(fun _ -> ref [])
        in
        items := !items @ [ item ]);
    Map.of_iteri_exn
      (module Namespace)
      ~iteri:(Hashtbl.map h ~f:( ! ) |> Hashtbl.iteri)

  module Std = struct
    module Ops = struct
      module ControlFlow = struct
        let ident =
          `Concrete
            { crate = "std"; path = Non_empty_list.[ "ops"; "ControlFlow" ] }

        let typ (break : ty) (continue : ty) : ty =
          TApp { ident; args = [ GType break; GType continue ] }

        let _make (name : string) (e : expr) (typ : ty) : expr =
          let constructor =
            `Concrete
              {
                crate = "std";
                path = Non_empty_list.("ops" :: "ControlFlow" :: [ name ]);
              }
          in
          {
            e with
            e =
              Construct
                {
                  constructor;
                  constructs_record = false;
                  base = None;
                  fields = [ (`TupleField (0, 1), e) ];
                };
            typ;
          }

        let break (e : expr) (continue_type : ty) : expr =
          _make "Break" e (typ e.typ continue_type)

        let continue (e : expr) (break_type : ty) : expr =
          _make "Continue" e (typ break_type e.typ)
      end
    end
  end
end
