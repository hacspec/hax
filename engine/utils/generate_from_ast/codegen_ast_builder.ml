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

let mk_builder (provided_fields : string list)
    ((record, enum) : Datatype.t * Datatype.t) =
  let ty = record.name in
  let record, variants =
    match (record.kind, enum.kind) with
    | Record record, Variant variants -> (record, variants)
    | _ -> failwith "mk_builder: bad kinds of datatypes"
  in
  let record_names = List.map ~f:fst record in
  let args =
    record
    |> List.filter
         ~f:(fst >> List.mem ~equal:[%eq: string] provided_fields >> not)
    |> List.filter ~f:(fun (_, ty) -> not ([%eq: string] ty.Type.typ enum.name))
    |> List.map ~f:(fun (name, ty) -> (true, name, ty))
  in
  let field_name_raw, _ =
    List.find ~f:(fun (_, ty) -> [%eq: string] ty.Type.typ enum.name) record
    |> Option.value_exn
  in
  List.map
    ~f:(fun Variant.{ name; payload } ->
      let extra_lb = ref "" in
      let args =
        args
        @
        match payload with
        | VariantPayload.Record fields ->
            fields
            |> List.map ~f:(fun (name, ty) ->
                   ( true,
                     (if List.mem ~equal:[%eq: string] record_names name then (
                        let name' = "inner_" ^ name in
                        (* if not ([%eq: string] field_name_raw name) then *)
                        extra_lb :=
                          !extra_lb ^ "let " ^ name ^ " = " ^ name' ^ " in\n";
                        name')
                      else name),
                     ty ))
        | Tuple types ->
            List.mapi ~f:(fun i ty -> (false, "x" ^ Int.to_string i, ty)) types
        | None -> []
      in
      let sargs =
        List.map
          ~f:(fun (named, name, ty) ->
            (if named then "~" else "") ^ "(" ^ name ^ ":" ^ print_ty ty ^ ")")
          args
        |> String.concat ~sep:" "
      in
      let head = "let " ^ ty ^ "_" ^ name ^ " " ^ sargs ^ ": " ^ ty ^ " = " in
      let spayload =
        match payload with
        | Record record -> print_record record
        | Tuple types ->
            List.mapi ~f:(fun i ty -> ("x" ^ Int.to_string i, ty)) types
            |> print_tuple
        | None -> ""
      in
      let body =
        "let " ^ field_name_raw ^ ": " ^ enum.name ^ " = " ^ !extra_lb ^ "\n"
        ^ name ^ " " ^ spayload ^ " in"
      in
      let body = body ^ print_record record in
      head ^ body)
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
  let body = data |> List.map ~f:(mk_builder []) |> String.concat ~sep:"\n\n" in
  let spanned =
    data |> List.map ~f:(mk_builder [ "span" ]) |> String.concat ~sep:"\n\n"
  in
  {|
open! Prelude
open! Ast


module Make (F : Features.T) = struct
  open Ast.Make(F)

module Explicit = struct
|}
  ^ body
  ^ {|
end

  module type SPAN = sig val span: span end
  module Make(Span: SPAN) = struct
    open Span
    |}
  ^ spanned ^ {|
  end

end
|}
