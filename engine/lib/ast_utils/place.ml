(** Quoting the {{: https://doc.rust-lang.org/reference/expressions.html#place-expressions-and-value-expressions }Rust Reference}, "a place expression is an expression that represents a memory location".

This module represent places and provides helpers around them.  *)

open! Prelude
open Ast

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST
  module Destruct = Ast_utils_syntax.Destruct (F)
  module Construct = Ast_utils_syntax.Construct (F)

  type t = { place : place; span : span; typ : ty }

  and place =
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
    | App { f = { e = GlobalVar (`Primitive Deref); _ }; args = [ e ]; _ } -> (
        match of_expr e with
        | Some { place = IndexProjection _; _ } as value -> value
        | _ -> wrap @@ Deref e)
    | LocalVar i -> wrap @@ LocalVar i
    | App
        {
          f = { e = GlobalVar (`Projector _ as projector); _ };
          args = [ place ];
          generic_args = _;
          impl = _;
        (* TODO: see issue #328 *)
        } ->
        let* place = of_expr place in
        wrap @@ FieldProjection { place; projector }
    | App
        {
          f = { e = GlobalVar f; _ };
          args = [ place; index ];
          generic_args = _;
          impl = _;
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
          impl = _;
        (* TODO: see issue #328 *)
        }
      when Global_ident.eq_name Core__ops__index__IndexMut__index_mut f ->
        (* Note that here, we allow any type to be `index_mut`ed:
           Hax translates that to `Rust_primitives.Hax.update_at`.
           This will typecheck IFF there is an implementation.
        *)
        let* typ = Destruct.Ty.mut_ref e.typ in
        let* place = Destruct.Expr.mut_borrow place in
        let* place = of_expr place in
        let place = IndexProjection { place; index } in
        Some { place; span = e.span; typ }
    | _ -> None

  let rec to_expr (p : t) : expr =
    match p.place with
    | LocalVar v ->
        let e : expr' = LocalVar v in
        { e; typ = p.typ; span = p.span }
    | Deref e -> Construct.Expr.app' (`Primitive Deref) [ e ] p.span p.typ
    | FieldProjection { place; projector } ->
        let e = to_expr place in
        Construct.Expr.app' projector [ e ] p.span p.typ
    | IndexProjection { place; index } ->
        let e = to_expr place in
        Construct.Expr.app Core__ops__index__Index__index [ e; index ] p.span
          p.typ

  let expect_deref_mut (p : t) : t option =
    match p.place with
    | Deref e ->
        let* e = Destruct.Expr.deref_mut_app e in
        let* e = Destruct.Expr.mut_borrow e in
        of_expr e
    | _ -> None

  let expect_allowed_deref_mut (p : t) : t option =
    let* p = expect_deref_mut p in
    if deref_mut_allowed p.typ then Some p else None

  let skip_allowed_deref_mut (p : t) : t =
    Option.value ~default:p (expect_deref_mut p)
end
