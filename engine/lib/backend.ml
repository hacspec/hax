open Utils
open Base
open Ast

let renamed_identifiers lvl = function
  | `Concrete Ast.{ crate = "hacspec_lib"; path } ->
      let last_chunk =
        match Non_empty_list.last path with
        | "U128_from_le_bytes" -> "uint128_from_le_bytes"
        | "new" -> "new_seq"
        | "ZERO" -> "zero"
        | last -> last
      in
      `Concrete
        Ast.{ crate = "hacspec_lib_tc"; path = Non_empty_list.[ last_chunk ] }
  | `Concrete
      Ast.
        {
          crate = "secret_integers";
          path = Non_empty_list.[ ("U128" | "U32" | "U8") ];
        }
    when [%matches? Ast_utils.ExprLevel] lvl ->
      `Concrete
        Ast.{ crate = "hacspec_lib_tc"; path = Non_empty_list.[ "secret" ] }
  | `Concrete Ast.{ crate = "dummy"; path } ->
      `Concrete
        Ast.{ crate = "hacspec"; path = Non_empty_list.[ "lib"; last path ] }
  | x -> x

module Options = struct
  type operator = string

  type t = {
    header : string;  (** a module header to inline *)
    operators : operator GlobalIdent.Map.t;
    output_directory : string;
    json_input : string;
    renamed_identifiers :
      Ast_utils.visit_level -> GlobalIdent.t -> GlobalIdent.t;
  }
  (* [@@deriving show] *)

  let mk_default =
    {
      header = "";
      operators = Map.empty (module GlobalIdent);
      output_directory = "out";
      json_input = "";
      renamed_identifiers;
    }
end

module type T = sig
  module InputLanguage : Features.T
  module AST : Ast.T

  module U : sig
    module Mappers : sig
      val rename_global_idents_item :
        (Ast_utils.visit_level -> global_ident -> global_ident) ->
        AST.item ->
        AST.item
    end
  end

  module BackendOptions : sig
    type t
  end

  val apply_phases :
    Options.t -> BackendOptions.t -> Ast.Rust.item -> AST.item list

  val translate :
    Options.t -> BackendOptions.t -> AST.item list -> Raw_thir_ast.output

  val name : string
end

let parse_list_json (parse : Yojson.Safe.t -> 'a) (input : Yojson.Safe.t) :
    'a list =
  match input with
  | `List l -> List.map ~f:parse l
  | _ -> failwith "parse_list_json: not a list"

let read_json (path : string) =
  let input =
    In_channel.with_open_bin path In_channel.input_all
    |> Yojson.Safe.from_string
  in
  let items = parse_list_json Raw_thir_ast.parse_item input in
  List.map
    ~f:(fun item ->
      try
        Result.map_error ~f:Import_thir.show_error (Import_thir.c_item item)
        |> Result.ok_or_failwith
      with Failure e -> failwith e)
    items
