open Thir_elab.Raw_thir_ast
open Core
open Thir_elab.Utils
open Thir_elab.Print_fstar
open Thir_elab
open Desugar_utils

module DesugarToFStar =
[%functor_application
Reject.RawOrMutPointer Features.Rust |> Resugar_for_loop.Make
|> Desugar_direct_and_mut.Make |> Reject.Continue
|> Desugar_drop_references.Make
|> (fun X ->
     (Desugar_mutable_variable.Make (module X))
       (module struct
         let early_exit = Fn.id
       end))
|> Reject.NotFStar |> Identity]

let parse_list_json (parse : Yojson.Safe.t -> 'a) (input : Yojson.Safe.t) :
    'a list =
  match input with
  | `List l -> List.map ~f:parse l
  | _ -> failwith "parse_list_json: not a list"

let () = Printexc.record_backtrace true;;

let path =
  if Array.length Sys.argv <> 2 then (
    print_endline "Usage thir-elab /path/to/the/thir'/file.json";
    exit 1)
  else Sys.argv.(1)
in
let input = In_channel.read_all path |> Yojson.Safe.from_string in
try
  let items = parse_list_json parse_item input in
  prerr_endline "Parsed";
  let converted_items =
    List.map
      ~f:(fun item ->
        try Result.map_error ~f:Import_thir.show_error (Import_thir.c_item item)
        with Failure e -> Error e)
      items
  in
  prerr_endline "Converted";
  print_endline "module Example";
  List.iter
    ~f:(fun item ->
      print_endline "";
      print_endline
        (match item with
        | Ok item ->
            let item =
              try
                let r = DesugarToFStar.ditem item in
                DebugBindDesugar.export ();
                r
              with e ->
                DebugBindDesugar.export ();
                raise e
            in
            decl_to_string (pitem item)
        | Error err -> "Convertion error: " ^ err))
    converted_items
with e -> print_endline (ParseError.pp e)
