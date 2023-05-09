open Circus_engine
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
  let run (type options_type)
      (module M : Backend.T with type BackendOptions.t = options_type)
      (backend_options : options_type) : Raw_thir_ast.output =
    let open M in
    options.input
    |> List.map ~f:(fun item ->
           try
             Result.map_error ~f:Import_thir.show_error
               (Import_thir.c_item item)
             |> Result.ok_or_failwith
           with Failure e -> failwith e)
    |> List.concat_map ~f:(apply_phases backend_options)
    |> List.map ~f:(U.Mappers.rename_global_idents_item renamed_identifiers)
    |> translate backend_options
  in
  try
    match options.backend.backend with
    | Fstar -> run (module Fstar_backend.FStarBackend) ()
    | Coq -> run (module Coq_backend.CoqBackend) ()
    | Easycrypt -> run (module Easycrypt_backend.ECBackend) ()
  with Diagnostics.Error x ->
    { diagnostics = [ Diagnostics.to_thir_diagnostic x ]; files = [] }

let main () =
  let finish = Phase_utils.DebugBindPhase.export in
  (try
     let results = run () in
     Raw_thir_ast.to_json_output results
     |> Yojson.Safe.pretty_to_string |> print_endline
   with exn ->
     finish ();
     raise exn);
  finish ()
