(* open Ast *)
open! Utils
open Base
module PatBase = To_patterns_base.Make (Features.Rust)
module AST = Ast.Make (Features.Rust)

let pattern_prefix = "_PATTERN_"
let wildcard_prefix = "WILDCARD_"

let to_binding binding =
  if String.is_prefix ~prefix:wildcard_prefix binding then "_" else binding

type result = { id : string; pattern : string }

class ['self] pattern_printer =
  object (self : 'self)
    inherit ['self] PatBase.pattern_printer as super

    method! of_ty ty =
      match ty with
      | TParam { name; _ } -> (
          match String.chop_prefix ~prefix:pattern_prefix name with
          | Some binding -> to_binding binding
          | None -> super#of_ty ty)
      | _ -> super#of_ty ty

    method! of_pat pat =
      match pat.p with
      | PBinding { var; subpat; _ } -> (
          match String.chop_prefix ~prefix:pattern_prefix var.name with
          | Some binding -> (
              match subpat with
              | None -> to_binding binding
              | Some (subpat, _) ->
                  "(" ^ self#of_pat subpat ^ ") as " ^ to_binding binding)
          | None -> super#of_pat pat)
      | _ -> super#of_pat pat

    method! of_expr expr =
      match expr.e with
      | LocalVar name -> (
          match String.chop_prefix ~prefix:pattern_prefix name.name with
          | Some binding -> to_binding binding
          | None -> super#of_expr expr)
      | _ -> super#of_expr expr

    val mutable guards = []

    method push_guard (guard : string -> string) : string =
      let name = List.length guards |> Int.to_string |> ( ^ ) "guarded_var_" in
      guards <- guard name :: guards;
      name

    method! of_Local_ident__t local_ident =
      "{ name = " ^ local_ident.name ^ "; _ }"

    method! of_concrete_ident concrete_ident =
      "{def_id = "
      ^ [%show: Concrete_ident_inner_types.Imported.def_id]
          concrete_ident.def_id
      ^ "; kind = "
      ^ [%show: Concrete_ident_inner_types.Kind.t] concrete_ident.kind
      ^ "}"

    method item : AST.item -> result option =
      fun item ->
        match item.v with
        | Fn fn -> (
            let name =
              Concrete_ident.DefaultViewAPI.to_definition_name fn.name
            in
            match split_str ~on:"__" name with
            | [ id; kind ] ->
                let pattern =
                  match kind with
                  | "expr" -> self#of_expr fn.body
                  | "type" -> (List.last_exn fn.params).typ |> self#of_ty
                  | _ -> failwith ("unexpected kind " ^ kind)
                in
                Some { id; pattern }
            | _ -> None)
        | _ -> None

    method! of_span _ = "_"
    method! of_impl_expr _ = "_"
    method! of_trait_goal _ = "_"
    method! of_impl_ident _ = "_"
  end
