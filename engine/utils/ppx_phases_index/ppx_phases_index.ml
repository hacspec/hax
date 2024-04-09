open Base
open Ppxlib

let name = "phases_index"
let ( let* ) x f = Option.bind ~f x

let map_first_letter (f : string -> string) (s : string) =
  let first, rest = String.(prefix s 1, drop_prefix s 1) in
  f first ^ rest

let uppercase_first_char = map_first_letter String.uppercase

let locate_phases_directory () : string =
  let rec find path =
    match path with
    | path when String.(Stdlib.Filename.basename path = "phases") -> Some path
    | path when Stdlib.Sys.is_directory path ->
        Stdlib.Sys.readdir path
        |> Array.filter ~f:(fun name -> not (String.is_prefix ~prefix:"." name))
        |> Array.find_map ~f:(fun name ->
               find @@ Stdlib.Filename.concat path name)
    | _ -> None
  in
  find (Stdlib.Sys.getcwd ())
  |> Option.value_exn
       ~message:"ppx_phases_index: could not locate folder [phases]"

let list_phases loc : (string * string * _ option) list =
  let dir = locate_phases_directory () in
  Stdlib.Sys.readdir dir |> Array.to_list
  |> List.filter_map ~f:(fun filename ->
         let* module_name = String.chop_suffix ~suffix:".mli" filename in
         let* _ =
           match String.chop_suffix ~suffix:".pp" module_name with
           | Some _ -> None
           | None -> Some ()
         in
         let* phase_name = String.chop_prefix ~prefix:"phase_" module_name in
         let module_name = uppercase_first_char module_name in
         let phase_name = uppercase_first_char phase_name in
         Some (filename, module_name, phase_name))
  |> List.map ~f:(fun (filename, module_name, phase_name) ->
         let path = Stdlib.Filename.concat dir filename in
         let str =
           Stdlib.open_in path |> Lexing.from_channel |> Parse.interface
         in
         let str =
           List.filter
             ~f:(function { psig_desc = Psig_open _; _ } -> false | _ -> true)
             str
         in
         match str with
         | [ _ ] -> (module_name, phase_name, None)
         | [ { psig_desc = Psig_attribute attr; _ }; _ ] ->
             (module_name, phase_name, Some attr)
         | [] -> failwith ("Empty phase" ^ filename)
         | _ ->
             failwith
               ("Invalid phase" ^ filename ^ ": got "
               ^ Int.to_string (List.length str)))

let rename (l : (string * string) list) =
  let h (s : string) =
    List.find_map
      ~f:(fun (s', replace) -> if String.equal s s' then Some replace else None)
      l
    |> Option.value ~default:s
  in
  object
    inherit Ast_traverse.map
    method! string = h
    method! label = h

    method! longident =
      let rec r = function
        | Lapply (x, y) -> Lapply (r x, r y)
        | Ldot (x, y) -> Ldot (r x, h y)
        | Lident x -> Lident (h x)
      in
      r
  end

let expand ~(ctxt : Expansion_context.Extension.t) (str : structure_item) :
    structure_item =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let (module S) = Ppxlib.Ast_builder.make loc in
  let modules =
    list_phases loc
    |> List.map ~f:(fun (module_name, phase_name, attrs) ->
           let h x = { txt = Lident x; loc } in
           let original =
             S.pmod_ident { txt = Ldot (Lident module_name, "Make"); loc }
           in
           let b =
             S.module_binding
               ~name:{ txt = Some phase_name; loc }
               ~expr:original
           in
           let attrs = Option.to_list attrs in
           let attrs =
             List.map
               ~f:(fun attr ->
                 let n = attr.attr_name in
                 if String.equal n.txt "ocaml.text" then
                   { attr with attr_name = { n with txt = "ocaml.doc" } }
                 else attr)
               attrs
           in
           let b = { b with pmb_attributes = attrs } in
           S.pstr_module b)
  in
  S.pstr_include (S.include_infos (S.pmod_structure modules))

let ext =
  Extension.V3.declare name Extension.Context.structure_item
    Ast_pattern.(pstr (__ ^:: nil))
    expand

let rule = Ppxlib.Context_free.Rule.extension ext
let () = Ppxlib.Driver.register_transformation ~rules:[ rule ] name
