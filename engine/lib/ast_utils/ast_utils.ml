open! Prelude
open Ast

(* module TypedLocalIdent = Ast_utils_sets.TypedLocalIdent *)

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST
  module TypedLocalIdent = Typed_local_ident.Make (F)
  module Reducers = Ast_utils_browse.Reducers (F)
  module Mappers = Ast_utils_browse.Mappers (F)
  module Construct = Ast_utils_syntax.Construct (F)
    module Destruct = Ast_utils_syntax.Destruct (F)
    module Place = Place.Make(F)

  module Sets = struct
    include Ast_utils_sets
    module TypedLocalIdent = M (TypedLocalIdent)
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
    | App { f = { e = GlobalVar f; _ }; args = [ e ]; _ }
      when Global_ident.eq_name Rust_primitives__unsize f ->
        e
    | _ -> e

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

  module LiftToFullAst = struct
    let expr : AST.expr -> Ast.Full.expr = Stdlib.Obj.magic
    let item : AST.item -> Ast.Full.item = Stdlib.Obj.magic
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
          impl = _;
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
              {
                f;
                args = [ e ];
                generic_args = [];
                impl = None (* TODO: see issue #328 *);
              };
          typ;
          span;
        }
    | LhsArrayAccessor { e; typ; index; _ } ->
        let args = [ expr_of_lhs span e; index ] in
         Construct.Expr.app Core__ops__index__Index__index args span typ
    | LhsArbitraryExpr { e; _ } -> e

  let rec map_body_of_nested_lets (f : expr -> expr) (e : expr) : expr =
    match e.e with
    | Let { monadic; lhs; rhs; body } ->
        {
          e with
          e = Let { monadic; lhs; rhs; body = map_body_of_nested_lets f body };
        }
    | _ -> f e


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
