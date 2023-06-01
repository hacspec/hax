open Hax_engine
open Base

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

let read_options_from_stdin () : Raw_thir_ast.engine_options =
  In_channel.input_all In_channel.stdin
  |> Yojson.Safe.from_string |> Raw_thir_ast.parse_engine_options

let run () : Raw_thir_ast.output =
  let options = read_options_from_stdin () in
  (match options.backend.debug_engine with
  | Some path ->
      if not (Caml.Sys.file_exists path && Caml.Sys.is_directory path) then
        failwith
          [%string
            "Engine error: the environment variable HAX_ENGINE_DEBUG is set to \
             [%{path}] which was expected to be a valid existing directory. \
             Aborting."];
      Phase_utils.DebugBindPhase.enable path
  | None -> ());
  let run (type options_type)
      (module M : Backend.T with type BackendOptions.t = options_type)
      (backend_options : options_type) : Raw_thir_ast.file list =
    let open M in
    options.input
    |> List.concat_map ~f:(fun item ->
           try
             Result.map_error ~f:Import_thir.show_error
               (Import_thir.c_item item)
             |> Result.ok_or_failwith
           with Failure e -> failwith e)
    |> List.concat_map ~f:(apply_phases backend_options)
    |> List.map ~f:(U.Mappers.rename_global_idents_item renamed_identifiers)
    |> translate backend_options
  in
  let diagnostics, files =
    Diagnostics.try_ (fun () ->
        match options.backend.backend with
        | Fstar -> run (module Fstar_backend) ()
        | Coq -> run (module Coq_backend) ()
        | Easycrypt -> run (module Easycrypt_backend) ())
  in
  {
    diagnostics = List.map ~f:Diagnostics.to_thir_diagnostic diagnostics;
    files = Option.value ~default:[] files;
  }

let main () =
  let result = try Ok (run ()) with e -> Error e in
  Phase_utils.DebugBindPhase.export ();
  match result with
  | Ok results ->
      Raw_thir_ast.to_json_output results
      |> Yojson.Safe.pretty_to_string |> print_endline
  | Error exn -> raise exn
