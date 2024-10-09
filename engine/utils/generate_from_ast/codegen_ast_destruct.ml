open Base
open Utils
open Types

let rec print_ty (t : Type.t) =
  if String.is_prefix t.typ ~prefix:"prim___tuple_" then
    "(" ^ String.concat ~sep:" * " (List.map t.args ~f:print_ty) ^ ")"
  else
    "("
    ^ (if List.is_empty t.args then ""
      else "(" ^ String.concat ~sep:", " (List.map t.args ~f:print_ty) ^ ") ")
    ^ t.typ ^ ")"

let print_record_or_tuple is_record x =
  let l, sep, r = if is_record then ("{", ";", "}") else ("(", ",", ")") in
  l ^ String.concat ~sep (List.map ~f:fst x) ^ r

let print_record = print_record_or_tuple true
let print_tuple = print_record_or_tuple false

let print_record_type_or_tuple is_record x =
  let l, sep, r = if is_record then ("{", ";", "}") else ("(", "*", ")") in
  l
  ^ String.concat ~sep
      (List.map
         ~f:(fun (name, ty) ->
           (if is_record then name ^ ":" else "") ^ print_ty ty)
         x)
  ^ r

let print_record_type = print_record_type_or_tuple true

let print_tuple_type =
  List.map ~f:(fun ty -> ("", ty)) >> print_record_type_or_tuple false

let mk_builder ((record, enum) : Datatype.t * Datatype.t) =
  let ty = record.name in
  let record, variants =
    match (record.kind, enum.kind) with
    | Record record, Variant variants -> (record, variants)
    | _ -> failwith "mk_builder: bad kinds of datatypes"
  in
  let field_name_raw, _ =
    List.find ~f:(fun (_, ty) -> [%eq: string] ty.Type.typ enum.name) record
    |> Option.value_exn
  in
  List.map
    ~f:(fun Variant.{ name; payload } ->
      let id = ty ^ "_" ^ name in
      let inline_record = id in
      let type_decl =
        "\ntype " ^ inline_record ^ " = "
        ^
        match payload with
        | Record record -> print_record_type record
        | Tuple types -> types |> print_tuple_type
        | None -> "unit"
      in
      let head =
        "\nlet " ^ id ^ " (value: " ^ ty ^ ")" ^ ": " ^ inline_record
        ^ " option ="
      in
      let spayload =
        match payload with
        | Record record -> print_record record
        | Tuple types ->
            List.mapi ~f:(fun i ty -> ("x" ^ Int.to_string i, ty)) types
            |> print_tuple
        | None -> ""
      in
      type_decl ^ head ^ "\n  match value." ^ field_name_raw ^ " with\n    | "
      ^ name ^ " " ^ spayload ^ " -> Some "
      ^ (if String.is_empty spayload then "()" else spayload)
      ^ if List.length variants |> [%eq: int] 1 then "" else "\n    | _ -> None")
    variants
  |> String.concat ~sep:"\n\n"

let mk datatypes =
  let find name =
    List.find ~f:(fun dt -> [%eq: string] dt.Datatype.name name) datatypes
    |> Option.value_exn
  in
  let data =
    [
      (find "expr", find "expr'");
      (find "pat", find "pat'");
      (find "item", find "item'");
      (find "guard", find "guard'");
      (find "trait_item", find "trait_item'");
      (find "impl_expr", find "impl_expr_kind");
    ]
  in
  let body = data |> List.map ~f:mk_builder |> String.concat ~sep:"\n\n" in
  {|
open! Prelude
open! Ast

module Make (F : Features.T) = struct
  open Ast.Make(F)

|}
  ^ body ^ {|

end
|}
