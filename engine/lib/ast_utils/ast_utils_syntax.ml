open! Prelude
open Ast

module Misc (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST

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
end

module Construct (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST
  open Misc (F)

  let tuple_field_pat (len : int) (nth : int) (pat : pat) : field_pat =
    { field = `TupleField (nth, len); pat }

  module Ty = struct
    let never : ty =
      let ident =
        `Concrete (Concrete_ident.of_name Type Rust_primitives__hax__Never)
      in
      TApp { ident; args = [] }

    let unit : ty = TApp { ident = `TupleType 0; args = [] }

    let tuple' (tuple : ty list) : ty =
      let args = List.map ~f:(fun typ -> GType typ) tuple in
      TApp { ident = `TupleType (List.length tuple); args }

    let tuple : ty list -> ty = function [ ty ] -> ty | l -> tuple' l

    let hax_failure : ty =
      let ident = Concrete_ident.of_name Type Rust_primitives__hax__failure in
      TApp { ident = `Concrete ident; args = [] }
  end

  module Pat = struct
    let var (var : local_ident) (typ : ty) (span : span) : pat =
      let mut, mode = (Immutable, ByValue) in
      { p = PBinding { mut; mode; var; typ; subpat = None }; span; typ }

    let wild (typ : ty) (span : span) : pat = { p = PWild; span; typ }

    let tuple' ?(drop_tuple_1=true) span : field_pat list -> pat = function
      | [ { pat; _ } ] when drop_tuple_1 -> pat
      | args ->
          let is_record, is_struct = (false, true) in
          let name = `TupleCons (List.length args) in
          let p = PConstruct { name; args; is_record; is_struct } in
          { p; typ = Ty.tuple @@ List.map ~f:(fun p -> p.pat.typ) args; span }

    let tuple ?(drop_tuple_1=true) ?span (pats : pat list) : pat =
      let len = List.length pats in
      let span =
        let default () = Span.union_list @@ List.map ~f:(fun p -> p.span) pats in
        Option.value_or_thunk span ~default
      in
      List.mapi ~f:(tuple_field_pat len) pats |> tuple' ~drop_tuple_1 span
  end

  module Expr = struct
    let unit span : expr = { typ = Ty.unit; span; e = GlobalVar (`TupleCons 0) }
    let string_lit span s : expr = { span; typ = TStr; e = Literal (String s) }

    let let_ (lhs : pat) (rhs : expr) (body : expr) =
      if pat_is_expr lhs body then rhs
      else { body with e = Let { monadic = None; lhs; rhs; body } }

    let let_uncurried ((var, rhs) : local_ident * expr) (body : expr) : expr =
      let_ (Pat.var var rhs.typ rhs.span) rhs body

    let multiple_lets (bindings : (local_ident * expr) list) (body : expr) :
        expr =
      List.fold_right ~init:body ~f:let_uncurried bindings

    let seq (e1 : expr) (e2 : expr) : expr =
      let_ (Pat.wild e1.typ e1.span) e1 e2

    let tuple' ~(span : span) (args : expr list) : expr =
      let len = List.length args in
      let is_record, is_struct = (false, true) in
      let fields = List.mapi ~f:(fun i x -> (`TupleField (i, len), x)) args in
      let constructor = `TupleCons len in
      {
        e = Construct { constructor; fields; is_record; is_struct; base = None };
        typ = List.map ~f:(fun { typ; _ } -> typ) args |> Ty.tuple;
        span;
      }

    let tuple ~(span : span) : expr list -> expr = function
      | [ e ] -> e
      | args -> tuple' ~span args

    let app' ?impl f (args : expr list) span ret_typ =
      let typ = TArrow (List.map ~f:(fun arg -> arg.typ) args, ret_typ) in
      let e = GlobalVar f in
      let e = App { f = { e; typ; span }; args; generic_args = []; impl } in
      { e; typ = ret_typ; span }

    let app ?impl ?(kind : Concrete_ident.Kind.t = Value)
        (f_name : Concrete_ident.name) (args : expr list) span ret_typ =
      let f = `Concrete (Concrete_ident.of_name kind f_name) in
      app' ?impl f args span ret_typ

    let hax_failure' span (typ : ty) (context, kind) (ast : string) =
      let error = Diagnostics.pretty_print_context_kind context kind in
      let args = List.map ~f:(string_lit span) [ error; ast ] in
      app Rust_primitives__hax__failure args span typ

    let hax_failure span (typ : ty) (context, kind) (expr0 : Ast.Full.expr) =
      hax_failure' span typ (context, kind) (Print_rust.pexpr_str expr0)

    let tuple_projector span (tuple_typ : ty) (len : int) (nth : int)
        (type_at_nth : ty) : expr =
      let e = GlobalVar (`Projector (`TupleField (nth, len))) in
      { span; typ = TArrow ([ tuple_typ ], type_at_nth); e }
  end

  let unit_param (span : span) : param =
    let typ = Ty.unit in
    { pat = Pat.wild typ span; typ; typ_span = None; attrs = [] }
end

module Destruct (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST

  module Item = struct
    let functions (x : item) : (concrete_ident * expr) list =
      match x.v with
      | Fn { name; generics = _; body; params = _ } -> [ (name, body) ]
      | Impl { items; _ } ->
          List.filter_map
            ~f:(fun w ->
              match w.ii_v with
              | IIFn { body; params = _ } -> Some (w.ii_ident, body)
              | _ -> None)
            items
      | _ -> []
  end

  module Expr = struct
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
            impl = _;
          (* TODO: see issue #328 *)
          }
        when Concrete_ident.eq_name f f' ->
          Some e
      | _ -> None

    let concrete_app' : expr' -> concrete_ident option = function
      | App { f = { e = GlobalVar (`Concrete c); _ }; _ } -> Some c
      | _ -> None

    let deref_mut_app : expr -> expr option =
      concrete_app1 Core__ops__deref__DerefMut__deref_mut

    let local_var (e : expr) : expr option =
      match e.e with LocalVar _ -> Some e | _ -> None

    let rec let_bindings' (e : expr) : (pat * expr * ty) list * expr =
      match e.e with
      | Let { monadic = _; lhs; rhs; body } ->
          let bindings, body = let_bindings' body in
          ((lhs, rhs, e.typ) :: bindings, body)
      | _ -> ([], e)

    let let_bindings (e : expr) : (pat * expr) list * expr =
      let bindings, body = let_bindings' e in
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
      let typ = List.hd types |> Option.value ~default:body.typ in
      (List.map ~f:(fun (p, e, _) -> (p, e)) bindings, { body with typ })
  end

  module Ty = struct
    let arrow (typ : ty) : (ty list * ty) option =
      match typ with
      | TArrow (inputs, output) -> Some (inputs, output)
      | _ -> None

    let mut_ref (typ : ty) : ty option =
      match typ with TRef { mut = Mutable _; typ; _ } -> Some typ | _ -> None

    let never : ty -> bool = function
      | TApp { ident; _ } ->
          Global_ident.eq_name Rust_primitives__hax__Never ident
      | _ -> false

    let unit = [%matches? TApp { ident = `TupleType 0; _ }]
  end
end
