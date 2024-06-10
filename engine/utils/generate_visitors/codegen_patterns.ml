(** This module generates printers for values with holes of given
types.

For each type `t`, we generate the following methods:

`<t>: t -> `


 - `pat_of_t: t -> expr` -> _
 - `hole_of_t: t -> name option`
 - `guard_of_t: t -> name option`.

 *)

open Base
open Utils
open Types

let value = "v"
let parens s = if String.contains s ' ' then "(" ^ s ^ ")" else s
let concat sep : string list -> string = String.concat ~sep

let strlit s =
  if String.contains s '"' then "{pat|" ^ s ^ "|pat}" else "\"" ^ s ^ "\""

let concat_expr = concat " ^ "
let app : string list -> string = concat " "
let method_prefix = "of_"

let method_name path =
  let path = String.split ~on:'.' path in
  method_prefix ^ String.concat ~sep:"__" path

let rec of_type' (t : Type.t) : string =
  let prefix = if String.is_prefix ~prefix:"'" t.typ then "" else "self#" in
  app ((prefix ^ method_name t.typ) :: List.map ~f:of_type' t.args) |> parens

let of_type (v : string) (t : Type.t) : string = app [ of_type' t; v ]

let of_record_field (v : string) ((field, typ) : Record.field) : string =
  concat_expr
    [ strlit (field ^ " = "); of_type (v ^ "." ^ field) typ; strlit "; " ]

let of_record (v : string) (fields : Record.t) : string =
  concat_expr
    ([ strlit "{ " ] @ List.map ~f:(of_record_field v) fields @ [ strlit " }" ])

let of_variant (variant : Variant.t) : string =
  match variant.payload with
  | Record record ->
      variant.name ^ " payload -> "
      ^ concat_expr [ strlit variant.name; of_record "payload" record ]
  | Tuple types ->
      let typed_vars =
        List.mapi ~f:(fun i typ -> ("x" ^ Int.to_string i, typ)) types
      in
      let vars = List.map ~f:fst typed_vars in
      let pats = List.map ~f:(uncurry of_type) typed_vars in
      let pat = concat (" ^ " ^ strlit ", " ^ " ^ ") pats in
      let pat = concat_expr [ strlit "("; pat; strlit ")" ] in
      variant.name ^ " "
      ^ (concat ", " vars |> parens)
      ^ " -> "
      ^ concat_expr [ strlit variant.name; pat ]
  | None -> variant.name ^ " -> " ^ strlit variant.name

let of_datatype (v : string) (dt : Datatype.t) : string =
  match dt.kind with
  | Record record -> of_record v record
  | Variant variants ->
      "match " ^ v ^ " with\n"
      ^ concat "\n  |" (List.map ~f:of_variant variants)
  | TypeSynonym typ -> of_type v typ
  (* | Opaque when String.is_prefix ~prefix:"F." dt.name -> app [ "self#mk_unique_wildcard"; method_name dt.name |> strlit ] *)
  | Opaque -> (
      match String.chop_prefix ~prefix:"F." dt.name with
      | Some feature_name ->
          app [ "self#generic_of_feature"; feature_name |> strlit ]
      | None -> app [ "self#mk_unique_wildcard"; method_name dt.name |> strlit ]
      )

let mk_method (dt : Datatype.t) : string =
  let self_typ =
    if Type.is_tuple_name dt.name then
      String.concat ~sep:" * " dt.type_vars |> parens
    else app [ String.concat ~sep:", " dt.type_vars |> parens; dt.name ]
  in
  let meth_typ =
    let forall_clause = String.concat ~sep:" " dt.type_vars in
    let mkarr typ = concat " -> " [ typ; "string" ] in
    let arrs = List.map ~f:(mkarr >> parens) (dt.type_vars @ [ self_typ ]) in
    let arrs = arrs |> concat " -> " in
    List.filter ~f:(String.is_empty >> not) [ forall_clause; arrs ]
    |> String.concat ~sep:"."
  in
  concat " "
    [
      "method";
      method_name dt.name;
      ":";
      meth_typ;
      "=";
      "\n  fun";
      concat " " (List.map ~f:method_name dt.type_vars);
      "v";
      "->\n    ";
      of_datatype "v" dt;
    ]

let manual =
  {|
method of_list: 'a. ('a -> string) -> 'a list -> string
 = fun f args -> "[" ^ String.concat ~sep:"; " (List.map ~f args) ^ "]"

val mutable wildcards_state = Base.Hashtbl.create (module String)

method mk_unique_wildcard (hint : string) : string =
  let f = Option.value ~default:0 >> ( + ) 1 in
  let n = Hashtbl.update_and_return wildcards_state hint ~f in
  "_" ^ hint ^ "_" ^ Int.to_string n

method generic_of_feature name = "_ (* matches feature " ^ name ^ " *)"

method of_bool = function | true -> "true" | false -> "false"
method of_char c = Base.String.of_char_list ['\''; c; '\'']
method of_string s =
  let rec h level =
    let l, r =
      if level < 0 then ("\"", "\"")
      else
        let tag = String.make level 's' in
        ("{" ^ tag ^ "|", "|" ^ tag ^ "}")
    in
    if String.is_substring s ~substring:r then h (level + 1) else l ^ s ^ r
  in
  h (-1)

method of_todo = self#of_string
|}

let mk (dts : Datatype.t list) : string =
  let dts = Primitive_types.(tuples @ [ option ]) @ dts in
  let opaques =
    Visitors.collect_undefined_types dts
    |> List.filter ~f:([%matches? "bool" | "char" | "int" | "string"] >> not)
    |> List.filter ~f:([%matches? "todo"] >> not)
    |> List.map ~f:(fun name ->
           Datatype.{ name; type_vars = []; kind = Opaque })
  in
  let dts = dts @ opaques in
  let contents = List.map ~f:mk_method dts |> concat "\n\n" in
  Codegen_visitor.header ^ "class virtual ['self] " ^ "pattern_printer"
  ^ " = object (self : 'self)" ^ contents ^ "\n" ^ manual ^ "\nend" ^ "\nend"
