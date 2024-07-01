open Base
open Utils
open Types

let _main =
  let ocaml_file =
    Stdio.In_channel.stdin |> Lexing.from_channel
    |> Ppxlib_ast.Parse.implementation
  in
  let datatypes =
    type_declaration_of_structure ocaml_file
    |> List.filter ~f:(fun (path, _) ->
           (* We only look at certain types in the AST.ml module *)
           String.is_prefix ~prefix:"Make." path
           || List.mem ~equal:String.equal
                [ "mutability"; "literal"; "attrs"; "quote" ]
                path)
    |> List.map ~f:(fun (path, td) ->
           ( String.chop_prefix ~prefix:"Make." path
             |> Option.value ~default:path,
             td ))
    |> List.map ~f:(fun (path, type_decl) ->
           (path, Datatype.of_ocaml_result type_decl))
    |> List.filter_map ~f:(fun (path, dt) ->
           match dt with
           (* Use path as name, can be useful if used on something else than AST.ml *)
           | Result.Ok v -> Some Datatype.{ v with name = path }
           | _ -> None)
  in
  datatypes |> Codegen_visitor.mk |> Stdio.print_endline
