open Thir_elab.Raw_thir_ast
open Core
open Thir_elab.Utils
open Thir_elab
open Desugar_utils
(* open Cli_types *)

let import_options (o : Cli_types.options) (json_input : string) :
    Backend.Options.t =
  let d = Backend.Options.mk_default o.output_dir json_input in
  d

let () =
  match
    (Base.Sys.getenv "THIR_ELAB_OPTIONS", Base.Sys.getenv "THIR_ELAB_INPUT")
  with
  | Some options, Some input -> (
      let options =
        Cli_types.parse_options @@ Yojson.Safe.from_string options
      in
      match options.backend with
      | Fstar ->
          let open Fstar_backend.FStarBackend in
          let o : Backend.Options.t = import_options options input in
          let bo : BackendOptions.t = () in
          let items = Backend.read_json o.json_input in
          let items = List.concat_map ~f:(desugar o bo) items in
          let items =
            List.map
              ~f:(U.Mappers.rename_global_idents_item o.renamed_identifiers)
              items
          in
          translate o bo items)
  | _ ->
      Fstar_backend.register;
      Printexc.record_backtrace true;
      exit (Cmdliner.Cmd.eval (Backend.Registration.command ()))
