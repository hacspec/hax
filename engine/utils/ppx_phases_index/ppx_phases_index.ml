open Base
open Ppxlib

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

let list_phases loc : (string * string * string * _ option) list =
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
         | [ _ ] -> (filename, module_name, phase_name, None)
         | [ { psig_desc = Psig_attribute attr; _ }; _ ] ->
             (filename, module_name, phase_name, Some attr)
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

let expand_phases_index ~(ctxt : Expansion_context.Extension.t)
    (str : structure_item) : structure_item =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let (module S) = Ppxlib.Ast_builder.make loc in
  let modules =
    list_phases loc
    |> List.map ~f:(fun (_, module_name, phase_name, attrs) ->
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

let chop_ml_or_mli str =
  match String.chop_suffix ~suffix:".ml" str with
  | Some result -> Some result
  | None -> String.chop_suffix ~suffix:".mli" str

let filename_to_phase_constructor file_name =
  let phase_name =
    file_name |> String.rsplit2 ~on:'/' |> Option.map ~f:snd
    |> Option.value ~default:file_name
    |> String.chop_prefix ~prefix:"phase_"
    |> Option.value_exn
         ~message:
           ("`[%auto_phase_name]` can only be used in a phase, whose filename \
             starts with `phase_`. Current file is: [" ^ file_name ^ "]")
    |> chop_ml_or_mli
    |> Option.value_exn
         ~message:
           ("File name [" ^ file_name
          ^ "] was expected to end with a `.ml` or `.mli`")
  in
  phase_name |> String.split ~on:'_'
  |> List.map ~f:uppercase_first_char
  |> String.concat

let expand_add_phase_names ~(ctxt : Expansion_context.Extension.t)
    (typ : type_declaration) : structure_item =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let (module S) = Ppxlib.Ast_builder.make loc in
  let ptype_kind =
    match typ.ptype_kind with
    | Ptype_variant ctors ->
        let phases = list_phases loc in
        let extra =
          List.map
            ~f:(fun (filename, _, _, _) ->
              let name = filename_to_phase_constructor filename in
              let name = { txt = name; loc = S.loc } in
              let args = Pcstr_tuple [] in
              S.constructor_declaration ~name ~args ~res:None)
            phases
        in
        Ptype_variant (ctors @ extra)
    | _ -> failwith "expected variants"
  in
  let typ = { typ with ptype_kind } in
  S.pstr_type Recursive [ typ ]

let expand_auto_phase_name ~(ctxt : Expansion_context.Extension.t)
    (str : structure_item) : expression =
  let file_name = Expansion_context.Extension.input_name ctxt in
  let constructor = filename_to_phase_constructor file_name in
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let (module S) = Ppxlib.Ast_builder.make loc in
  let txt = Astlib.Longident.parse ("Diagnostics.Phase." ^ constructor) in
  S.pexp_construct { txt; loc = S.loc } None

let () =
  let rule_phases_index =
    let name = "phases_index" in
    Ppxlib.Context_free.Rule.extension
      (Extension.V3.declare name Extension.Context.structure_item
         Ast_pattern.(pstr (__ ^:: nil))
         expand_phases_index)
  in
  let rule_auto_phase_name =
    let name = "auto_phase_name" in
    Ppxlib.Context_free.Rule.extension
      (Extension.V3.declare name Extension.Context.expression
         Ast_pattern.(pstr (__ ^:: nil))
         expand_auto_phase_name)
  in
  let rule_expand_add_phase_names =
    let name = "add_phase_names" in
    Ppxlib.Context_free.Rule.extension
      (Extension.V3.declare name Extension.Context.structure_item
         Ast_pattern.(pstr (pstr_type drop (__ ^:: nil) ^:: nil))
         expand_add_phase_names)
  in
  Ppxlib.Driver.register_transformation
    ~rules:
      [ rule_phases_index; rule_auto_phase_name; rule_expand_add_phase_names ]
    "ppx_phases_index"
