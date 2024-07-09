open Ppxlib
open! Ppx_yojson_conv_lib.Yojson_conv.Primitives

let pp_core_type = Pprintast.core_type

let pp_label_declaration fmt label_decl =
  Stdlib.Format.pp_print_string fmt label_decl.pld_name.txt

let pp_constructor_declaration fmt cons_decl =
  Stdlib.Format.pp_print_string fmt cons_decl.pcd_name.txt

let pp_type_declaration fmt type_decl =
  Pprintast.structure_item fmt
    {
      pstr_loc = Astlib.Location.none;
      pstr_desc = Pstr_type (Nonrecursive, [ type_decl ]);
    }

type t =
  | UnsupportedCoreType of core_type
  | UnsupportedLabelDeclaration of label_declaration
  | UnsupportedConstructorDeclaration of constructor_declaration
  | UnsupportedTypeDeclaration of type_declaration
[@@deriving show]

open struct
  type t_string =
    | UnsupportedCoreType of string
    | UnsupportedLabelDeclaration of string
    | UnsupportedConstructorDeclaration of string
    | UnsupportedTypeDeclaration of string
  [@@deriving show, yojson]

  let into_string : t -> t_string = function
    | UnsupportedCoreType core_type ->
        UnsupportedCoreType ([%show: core_type] core_type)
    | UnsupportedLabelDeclaration label_declaration ->
        UnsupportedLabelDeclaration
          ([%show: label_declaration] label_declaration)
    | UnsupportedConstructorDeclaration constructor_declaration ->
        UnsupportedConstructorDeclaration
          ([%show: constructor_declaration] constructor_declaration)
    | UnsupportedTypeDeclaration type_declaration ->
        UnsupportedTypeDeclaration ([%show: type_declaration] type_declaration)
end

let yojson_of_t (e : t) = into_string e |> [%yojson_of: t_string]
let _ = pp_t_string (* just to silence OCaml warning *)

exception Error of t
