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

  let mk_default output_directory json_input =
    {
      header = "";
      operators = Map.empty (module GlobalIdent);
      output_directory;
      json_input;
      renamed_identifiers;
    }

  open Cmdliner

  let parse : t Term.t =
    let output_directory =
      Arg.(
        value & opt string "out"
        & info [ "o"; "output" ] ~docv:"OUTPUT_DIR"
            ~doc:"Directory in which the backend should output files.")
    in
    let json_input =
      Arg.(
        value
        & opt string "circus_frontend_export.json"
        & info [ "i"; "input" ] ~docv:"INPUT_JSON"
            ~doc:"Input JSON file (produced with `cargo circus`).")
    in

    Term.(const mk_default $ output_directory $ json_input)
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

    val parse : t Cmdliner.Term.t
  end

  val desugar : Options.t -> BackendOptions.t -> Ast.Rust.item -> AST.item list
  val translate : Options.t -> BackendOptions.t -> AST.item list -> unit
  val name : string
end

let parse_list_json (parse : Yojson.Safe.t -> 'a) (input : Yojson.Safe.t) :
    'a list =
  match input with
  | `List l -> List.map ~f:parse l
  | _ -> failwith "parse_list_json: not a list"

let read_json (path : string) =
  let input = In_channel.with_open_bin path In_channel.input_all |> Yojson.Safe.from_string in
  let items = parse_list_json Raw_thir_ast.parse_item input in
  List.map
    ~f:(fun item ->
      try
        Result.map_error ~f:Import_thir.show_error (Import_thir.c_item item)
        |> Result.ok_or_failwith
      with Failure e -> failwith e)
    items

module Registration : sig
  val register : (module T) -> unit
  val command : unit -> unit Cmdliner.Cmd.t
end = struct
  module StringHashtbl = Hashtbl.M (String)

  let backends : (module T) StringHashtbl.t = Hashtbl.create (module String)
  let backend_of_name = Hashtbl.find_exn backends

  let register (module X : T) =
    match Hashtbl.add backends ~key:X.name ~data:(module X) with
    | `Ok -> ()
    | `Duplicate ->
        failwith @@ "Error while registrating backend [" ^ X.name
        ^ "]: a backend with a same name already exists"

  open Cmdliner
  (* module U = Ast_utils.Make (Features.Rust) *)

  let commands () : unit Cmd.t list =
    Hashtbl.to_alist backends
    |> List.map ~f:(fun (name, (module B : T)) ->
           let info = Cmd.info name in
           let opts = B.BackendOptions.parse in
           let f (o : Options.t) bo =
             let items = read_json o.json_input in
             let h lvl x = x in
             let items = List.concat_map ~f:(B.desugar o bo) items in
             let items =
               List.map
                 ~f:
                   (B.U.Mappers.rename_global_idents_item o.renamed_identifiers)
                 items
             in
             B.translate o bo items
           in
           Cmd.v info Term.(const f $ Options.parse $ opts))

  let command () : unit Cmd.t =
    let info =
      Cmd.info "circus-engine"
        ~doc:
          ("Backend to use (available: "
          ^ String.concat ~sep:", " (Hashtbl.keys backends)
          ^ ")")
    in
    Cmd.group info (commands ())
end
