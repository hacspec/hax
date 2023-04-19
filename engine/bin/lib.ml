open Circus_engine.Raw_thir_ast
open Circus_engine.Utils
open Circus_engine
open Desugar_utils
open Base

let read_options_from_stdin () : Raw_thir_ast.options =
  In_channel.input_all In_channel.stdin
  |> Yojson.Safe.from_string |> Raw_thir_ast.parse_options

let run () : Raw_thir_ast.output =
  let options = read_options_from_stdin () in
  let run (type options_type)
      (module M : Backend.T with type BackendOptions.t = options_type)
      (backend_options : options_type) : Raw_thir_ast.output =
    let open M in
    let o : Backend.Options.t = Backend.Options.mk_default in
    options.input
    |> List.map ~f:(fun item ->
           try
             Result.map_error ~f:Import_thir.show_error
               (Import_thir.c_item item)
             |> Result.ok_or_failwith
           with Failure e -> failwith e)
    |> List.concat_map ~f:(desugar o backend_options)
    |> List.map ~f:(U.Mappers.rename_global_idents_item o.renamed_identifiers)
    |> translate o backend_options
  in
  try
    match options.backend with
    | Fstar -> run (module Fstar_backend.FStarBackend) ()
    | Coq -> run (module Coq_backend.CoqBackend) ()
    | Easycrypt -> run (module Easycrypt_backend.ECBackend) ()
  with Diagnostics.Error x ->
    { diagnostics = [ Diagnostics.to_thir_diagnostic x ]; files = [] }

let main () =
  print_endline @@ Yojson.Safe.pretty_to_string @@ Raw_thir_ast.to_json_output
  @@ run ()
