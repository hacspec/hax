(** This module defines a subset of OCaml inductives as a nice and
simple AST *)

open Base
open! Utils
open Errors

(** Describe what is a type expression, reflects OCaml's `core_type`. *)
module Type = struct
  let tuple_prefix = "prim___tuple_"
  let is_tuple_name = String.is_prefix ~prefix:tuple_prefix
  let tuple_name (len : int) : string = tuple_prefix ^ Int.to_string len
  let unit_name : string = "unit___"

  let lident_to_string lident =
    Astlib.Longident.flatten lident |> String.concat ~sep:"."

  type t = { typ : string; args : t list } [@@deriving show, yojson]

  let tuple args =
    match args with
    | [] -> { typ = unit_name; args }
    | [ typ ] -> typ
    | _ -> { typ = tuple_name (List.length args); args }

  let unsupported v = raise (Error (UnsupportedCoreType v))

  open Ppxlib

  let rec of_ocaml (t : core_type) : t =
    match t.ptyp_desc with
    | Ptyp_var typ -> { typ = "'" ^ typ; args = [] }
    | Ptyp_tuple types -> List.map ~f:of_ocaml types |> tuple
    | Ptyp_constr (lident, types) ->
        { typ = lident_to_string lident.txt; args = List.map ~f:of_ocaml types }
    | _ -> unsupported t
end

(** Describe what is a record, reflects OCaml's `label_declaration`. *)
module Record = struct
  type field = string * Type.t [@@deriving show, yojson]
  type t = field list [@@deriving show, yojson]

  let unsupported v = raise (Error (UnsupportedLabelDeclaration v))

  open Ppxlib

  let field_of_ocaml (label_decl : label_declaration) : field =
    (match label_decl.pld_mutable with
    | Mutable -> unsupported label_decl
    | _ -> ());
    (label_decl.pld_name.txt, Type.of_ocaml label_decl.pld_type)

  let of_ocaml : label_declaration list -> t = List.map ~f:field_of_ocaml
end

(** Describe what is a variant payload, reflects OCaml's `construtor_arguments`. *)
module VariantPayload = struct
  type t = Record of Record.t | Tuple of Type.t list | None
  [@@deriving show, yojson]

  open Ppxlib

  let of_ocaml (cons_decl : constructor_arguments) : t =
    match cons_decl with
    | Pcstr_tuple [] -> None
    | Pcstr_tuple [ typ ] -> (
        match typ.ptyp_desc with
        | Ptyp_tuple types -> Tuple (List.map ~f:Type.of_ocaml types)
        | _ -> Tuple [ Type.of_ocaml typ ])
    | Pcstr_tuple types -> Tuple (List.map ~f:Type.of_ocaml types)
    | Pcstr_record label_decls -> Record (Record.of_ocaml label_decls)
end

(** Describe what is a variant, reflects OCaml's `constructor_declaration`. *)
module Variant = struct
  type t = { name : string; payload : VariantPayload.t }
  [@@deriving show, yojson]

  let unsupported v = raise (Error (UnsupportedConstructorDeclaration v))

  open Ppxlib

  let of_ocaml (cons_decl : constructor_declaration) : t =
    if List.is_empty cons_decl.pcd_vars |> not then unsupported cons_decl;
    let payload = VariantPayload.of_ocaml cons_decl.pcd_args in
    { name = cons_decl.pcd_name.txt; payload }
end

(** A result type. *)
module Result = struct
  type ('r, 'e) t = Ok of 'r | Error of 'e [@@deriving show, yojson]
end

(** Describe what is a datatype, reflects ppx' `type_declaration`. *)
module Datatype = struct
  type kind =
    | Record of Record.t
    | Variant of Variant.t list
    | TypeSynonym of Type.t
    | Opaque
        (** `Opaque` is not produced by `of_ocaml` below; it is used by `codegen_visitor` to generate identity visitors *)
  [@@deriving show, yojson]

  type t = { name : string; type_vars : string list; kind : kind }
  [@@deriving show, yojson]

  let unsupported v = raise (Error (UnsupportedTypeDeclaration v))

  let of_ocaml (type_decl : Ppxlib.type_declaration) : t =
    let open Ppxlib in
    let name = type_decl.ptype_name.txt in
    let type_vars =
      List.map
        ~f:(fun (t, _) ->
          match t.ptyp_desc with
          | Ptyp_var n -> "'" ^ n
          | _ -> unsupported type_decl)
        type_decl.ptype_params
    in
    if List.is_empty type_decl.ptype_cstrs |> not then unsupported type_decl;
    let kind =
      match (type_decl.ptype_kind, type_decl.ptype_manifest) with
      | Ptype_abstract, Some typ -> TypeSynonym (Type.of_ocaml typ)
      | Ptype_variant cons_decls, None ->
          Variant (List.map ~f:Variant.of_ocaml cons_decls)
      | Ptype_record label_decls, None -> Record (Record.of_ocaml label_decls)
      | _ -> unsupported type_decl
    in
    { name; kind; type_vars }

  let of_ocaml_result (type_decl : Ppxlib.type_declaration) :
      (t, Errors.t) Result.t =
    try Result.Ok (of_ocaml type_decl) with Errors.Error e -> Result.Error e
end
