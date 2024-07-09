(** This module encodes several primitive OCaml types as Datatype.t so
that visitors can be generated automatically for them as well. *)

open Base
open! Utils
open Types

(** Helper to produce type variable. *)
let ty_var typ = Type.{ typ; args = [] }

(** Produces a datatype description for tuples of a given length. *)
let mk_tuple len =
  let type_vars = List.init len ~f:(fun i -> "'t" ^ Int.to_string i) in
  let name = Type.tuple_name len in
  let types = List.map ~f:ty_var type_vars in
  let payload = VariantPayload.Tuple types in
  let kind = Datatype.Variant [ Variant.{ name = ""; payload } ] in
  Datatype.{ name; type_vars; kind }

(** Common sizes of tuples. *)
let tuples = List.map ~f:mk_tuple [ 2; 3; 4 ]

(** Datatype description for the option type. *)
let option =
  let kind =
    Datatype.Variant
      [
        Variant.
          { name = "Some"; payload = VariantPayload.Tuple [ ty_var "'a" ] };
        Variant.{ name = "None"; payload = VariantPayload.None };
      ]
  in
  Datatype.{ name = "option"; type_vars = [ "'a" ]; kind }
