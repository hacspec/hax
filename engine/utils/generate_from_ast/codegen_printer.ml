open Base
open Utils
open Types

type state = { names_with_doc : string list }

let ( let* ) x f = Option.bind ~f x
let super_types_list = [ "expr"; "pat"; "guard"; "arm"; "item" ]

let get_super_type ty =
  List.find ~f:(fun s -> String.equal (s ^ "'") ty) super_types_list

let get_child_type ty =
  if List.mem ~equal:String.equal super_types_list ty then Some (ty ^ "'")
  else None

let do_not_override_prefix = "_do_not_override_"

let is_hidden_method =
  let list =
    [
      "expr'_App";
      "expr'_Construct";
      "ty_TApp";
      "lhs_LhsFieldAccessor";
      "local_ident";
      "pat'_PConstruct";
      "expr'_GlobalVar";
      "variant";
      "item'_Type";
    ]
  in
  List.mem ~equal:[%eq: string] list

let lazy_doc_manual_definitions = [ "_do_not_override_lazy_of_generics" ]

let rec of_ty (state : state) (call_method : string -> ty:string -> string)
    (t : Type.t) : ((unit -> string) -> string -> string) option =
  let* args =
    List.fold t.args ~init:(Some []) ~f:(fun acc x ->
        let* acc = acc in
        let* x = of_ty state call_method x in
        Some (x :: acc))
    |> Option.map ~f:List.rev
  in
  match (t.typ, args) with
  | "option", [ inner ] ->
      Some
        (fun pos value ->
          "(match " ^ value ^ " with | None -> None | Some value -> Some ("
          ^ inner pos "value" ^ "))")
  | "list", [ inner ] ->
      Some
        (fun pos value ->
          "(List.map ~f:(fun x -> " ^ inner pos "x" ^ ") " ^ value ^ ")")
  | "prim___tuple_2", [ fst; snd ] ->
      Some
        (fun pos value ->
          let base =
            "("
            ^ fst pos ("(fst " ^ value ^ ")")
            ^ ","
            ^ snd pos ("(snd " ^ value ^ ")")
            ^ ")"
          in
          let mk proj =
            "(let x = " ^ base ^ "in lazy_doc (fun tuple -> (" ^ proj
            ^ " tuple)#p) " ^ pos () ^ " x)"
          in
          match List.map ~f:(is_lazy_doc_typ state) t.args with
          | [ false; true ] -> mk "snd"
          | [ true; false ] -> mk "fst"
          | _ -> base)
      (* if String.is_prefix ~prefix:"F." (List.nth t.args 1 |> Option.value ~default:"") then "(let x = " ^ base ^ "in lazy_doc x)" else base) *)
  | "prim___tuple_3", [ fst; snd; thd ] ->
      Some
        (fun pos value ->
          "(let (value1, value2, value3) = " ^ value ^ " in ("
          ^ fst pos "value1" ^ "," ^ snd pos "value2" ^ "," ^ thd pos "value3"
          ^ "))")
  | _ when List.mem ~equal:[%eq: string] state.names_with_doc t.typ ->
      Some
        (fun pos value ->
          "(print#" ^ do_not_override_prefix ^ "lazy_of_" ^ t.typ
          ^ (if Option.is_some (get_super_type t.typ) then " ~super" else "")
          ^ " " ^ pos () ^ " " ^ value ^ ")")
  | _ -> Some (fun pos value -> "(" ^ value ^ ")")

and string_ty_of_ty' (state : state) (t : Type.t) =
  if String.is_prefix t.typ ~prefix:"prim___tuple_" then
    let args = List.map t.args ~f:(string_ty_of_ty' state) in
    let n = List.count args ~f:(String.is_suffix ~suffix:"lazy_doc)") in
    let base =
      "("
      ^ String.concat ~sep:" * " (List.map t.args ~f:(string_ty_of_ty' state))
      ^ ")"
    in
    if [%eq: int] n 1 then "(" ^ base ^ " lazy_doc)" else base
  else
    "("
    ^ (if List.is_empty t.args then ""
      else
        "("
        ^ String.concat ~sep:", " (List.map t.args ~f:(string_ty_of_ty' state))
        ^ ") ")
    ^ t.typ
    ^ (if List.mem ~equal:[%eq: string] state.names_with_doc t.typ then
       " lazy_doc"
      else "")
    ^ ")"

and is_lazy_doc_typ (state : state) = string_ty_of_ty' state >> is_lazy_doc_typ'
and is_lazy_doc_typ' = String.is_suffix ~suffix:"lazy_doc)"

let string_ty_of_ty (state : state) (t : Type.t) =
  let s = string_ty_of_ty' state t in
  match s with
  | "(generics lazy_doc)" ->
      "((generics lazy_doc * generic_param lazy_doc list * generic_constraint \
       lazy_doc list) lazy_doc)"
  | _ -> s

let meth_name' typ_name variant_name =
  typ_name ^ if String.is_empty variant_name then "" else "_" ^ variant_name

let meth_name typ_name variant_name =
  let meth = meth_name' typ_name variant_name in
  (if is_hidden_method meth then do_not_override_prefix else "") ^ meth

let print_variant state (call_method : string -> ty:string -> string)
    (register_position : string option -> string) (super_type : string option)
    (register_signature : string -> unit) (t_name : string) (v : Variant.t) :
    string =
  let meth_name = meth_name t_name v.name in
  let meth = "print#" ^ meth_name in
  let mk named fields =
    let head =
      v.name
      ^ (if named then " { " else " ( ")
      ^ String.concat ~sep:(if named then ";" else ",") (List.map ~f:fst fields)
      ^ (if named then " } " else ")")
      ^ " -> "
    in
    let args =
      List.map
        ~f:(fun (field_name, ty) ->
          let value =
            match of_ty state call_method ty with
            | Some f ->
                let pos = register_position (Some field_name) in
                f (fun _ -> pos) field_name
            | None -> field_name
          in
          let name = "~" ^ field_name ^ ":" in
          (if named then name else "") ^ "(" ^ value ^ ")")
        fields
    in
    let call =
      String.concat ~sep:" "
        (meth
        :: ((if Option.is_some super_type then [ "~super" ] else []) @ args))
    in
    let signature =
      let ty =
        List.map
          ~f:(fun (name, ty) ->
            let name = if named then name ^ ":" else "" in
            name ^ string_ty_of_ty state ty)
          fields
        |> String.concat ~sep:" -> "
      in
      let super =
        match super_type with
        | Some super_type -> " super:(" ^ super_type ^ ") -> "
        | None -> ""
      in
      register_signature
        ("method virtual " ^ meth_name ^ " : " ^ super ^ ty ^ " -> document")
    in
    head ^ call
  in
  "\n  | "
  ^
  match v.payload with
  | Record fields -> mk true fields
  | None -> v.name ^ " -> " ^ meth
  | Tuple types ->
      mk false (List.mapi ~f:(fun i ty -> ("x" ^ Int.to_string i, ty)) types)

let catch_errors_for = [ "expr"; "item"; "pat" ]

let print_datatype state (dt : Datatype.t)
    (register_entrypoint : string -> unit)
    (register_position : string -> string -> string option -> string) =
  let super_type = get_super_type dt.name in
  let sigs = ref [] in
  let method_name = do_not_override_prefix ^ "lazy_of_" ^ dt.name in
  let print_variants variants wrapper =
    let head =
      "(**/**) method " ^ method_name
      ^ (match super_type with Some t -> " ~(super: " ^ t ^ ")" | _ -> "")
      ^ " ast_position (value: " ^ dt.name ^ "): " ^ dt.name ^ " lazy_doc ="
    in
    let body =
      (if Option.is_some (get_child_type dt.name) then
       "\n    let super = value in"
      else "")
      ^ "\n    match value with"
      ^ String.concat ~sep:""
          (List.map
             ~f:(fun variant ->
               print_variant state
                 (fun name ~ty:_ -> name)
                 (register_position dt.name variant.Variant.name)
                 super_type
                 (fun s -> sigs := s :: !sigs)
                 dt.name variant)
             variants)
    in
    let body =
      "(print#wrap_" ^ dt.name ^ " ast_position value (" ^ body ^ "))"
    in
    let body = wrapper body in
    sigs :=
      ("method wrap_" ^ dt.name ^ " (_pos: ast_position) (_value: " ^ dt.name
     ^ ") (doc: document): document = doc")
      :: !sigs;
    let def =
      head ^ "lazy_doc (fun (value: " ^ dt.name ^ ") -> " ^ body
      ^ ") ast_position value"
    in
    if List.mem ~equal:[%eq: string] lazy_doc_manual_definitions method_name
    then "(* skipping " ^ method_name ^ " *) (**/**)"
    else def ^ "(**/**)"
  in
  let main =
    match dt.kind with
    | Variant variants -> print_variants variants Fn.id
    | Record record ->
        let wrapper =
          if List.exists ~f:(fst >> [%eq: string] "span") record then
            fun body ->
            "print#with_span ~span:value.span (fun _ -> " ^ body ^ ")"
          else Fn.id
        in
        let wrapper =
          if List.mem ~equal:[%eq: string] catch_errors_for dt.name then
            fun body ->
            "print#catch_exn print#error_" ^ dt.name ^ " (fun () -> "
            ^ wrapper body ^ ")"
          else wrapper
        in
        print_variants [ { name = ""; payload = Record record } ] wrapper
    | TypeSynonym ty ->
        print_variants [ { name = ""; payload = Tuple [ ty ] } ] (fun x -> x)
    | _ -> "(* Not translating " ^ dt.name ^ " *)"
  in
  let print =
    let name = "print_" ^ dt.name in
    let ty = "ast_position -> " ^ dt.name ^ " -> " in
    let body =
      "fun ast_position x -> (print#" ^ method_name ^ " ast_position x)#p"
    in
    if Option.is_none super_type then
      "method " ^ name ^ ": " ^ ty ^ " document = " ^ body
    else ""
  in
  let entrypoint =
    let name = "entrypoint_" ^ dt.name in
    let ty = dt.name ^ " -> " in
    let body = "print#print_" ^ dt.name ^ " AstPos_Entrypoint" in
    if Option.is_none super_type then (
      register_entrypoint (name ^ " : " ^ ty ^ " 'a");
      "method " ^ name ^ ": " ^ ty ^ " document = " ^ body)
    else ""
  in
  String.concat ~sep:"\n\n" (main :: print :: entrypoint :: !sigs)

let hardcoded =
  {|
module LazyDoc = struct
    type 'a lazy_doc =
      < compact : output -> unit
      ; pretty : output -> state -> int -> bool -> unit
      ; requirement : int
      ; p : document
      ; v : 'a
      ; ast_position : ast_position >
    let lazy_doc : 'a. ('a -> document) -> ast_position -> 'a -> 'a lazy_doc =
     fun to_document pos value ->
      let lazy_doc = ref None in
      let doc () =
        match !lazy_doc with
        | None ->
            let doc = to_document value in
            lazy_doc := Some doc;
            doc
        | Some doc -> doc
      in
      object (self)
        method requirement : requirement = requirement (doc ())
        method pretty : output -> state -> int -> bool -> unit =
          fun o s i b -> pretty o s i b (doc ())
        method compact : output -> unit = fun o -> compact o (doc ())
        method p = custom (self :> custom)
        method v = value
        method ast_position = pos
      end
end
open LazyDoc
|}

let class_prelude =
  {|
   method virtual with_span: span:span -> (unit -> document) -> document
   method virtual catch_exn : (string -> document) -> (unit -> document) -> document

   method virtual _do_not_override_lazy_of_local_ident: _
   method virtual _do_not_override_lazy_of_concrete_ident: _
|}

let mk datatypes =
  let datatypes =
    List.filter
      ~f:(fun dt -> not ([%eq: string] dt.Datatype.name "mutability"))
      datatypes
  in
  let state =
    let names_with_doc = List.map ~f:(fun dt -> dt.name) datatypes in
    let names_with_doc =
      "quote" :: "concrete_ident" :: "local_ident" :: names_with_doc
    in
    { names_with_doc }
  in
  let positions = ref [ "AstPos_Entrypoint"; "AstPos_NotApplicable" ] in
  let entrypoint_types = ref [] in
  let class_body =
    List.map
      ~f:(fun dt ->
        print_datatype state dt
          (fun x -> entrypoint_types := x :: !entrypoint_types)
          (fun ty variant field ->
            let pos =
              "AstPos_" ^ ty ^ "_" ^ variant
              ^ match field with Some field -> "_" ^ field | _ -> ""
            in
            positions := pos :: !positions;
            pos))
      datatypes
    |> String.concat ~sep:"\n\n"
  in
  let object_poly = String.concat ~sep:";\n " !entrypoint_types in
  let object_span_data_map =
    String.concat ~sep:"\n"
      (List.map
         ~f:(fun s ->
           let n = fst (String.lsplit2_exn ~on:':' s) in
           "method " ^ n ^ " = obj#" ^ n)
         !entrypoint_types)
  in
  let object_map =
    String.concat ~sep:"\n"
      (List.map
         ~f:(fun s ->
           let n = fst (String.lsplit2_exn ~on:':' s) in
           "method " ^ n ^ " x = f (fun obj -> obj#" ^ n ^ " x)")
         !entrypoint_types)
  in
  Printf.sprintf
    {|
open! Prelude
open! Ast
open PPrint
type ast_position = %s | AstPosition_Quote

%s

module Make (F : Features.T) = struct
   module AST = Ast.Make (F)
   open Ast.Make (F)

   class virtual base = object (print)
     %s
   end

   type ('span_data, 'a) object_type = <
        span_data : 'span_data;
        %s
     >

   let map (type span_data) (type a) (type b)
           (f: ((span_data, a) object_type -> a) -> b)
           : (unit, b) object_type = object
        method span_data: unit = ()
        %s
     end

   let map_span_data (type a) (type b) (type t)
          (obj: (a, t) object_type)
          (span_data: b)          
          : (b, t) object_type = object
        method span_data: b = span_data
        %s
     end
end
|}
    (String.concat ~sep:" | "
       (List.dedup_and_sort ~compare:String.compare !positions))
    hardcoded
    (class_prelude ^ class_body)
    object_poly object_map object_span_data_map
