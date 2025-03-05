(** Give a list of {!Types.Datatype.t}, this file generates an ocaml
module of visitors. *)

open Base
open Utils
open Types

(** What kind of visitor are we generating? *)
type kind = Map | MapReduce | Reduce

(** Helpers around kinds *)
include struct
  let is_reduce = function MapReduce | Reduce -> true | _ -> false
  let is_map = function Map | MapReduce -> true | _ -> false
end

(** Various helpers and constants *)
include struct
  let method_prefix = "visit_"
  let acc_var_prefix = "acc___"
  let acc_var_param = acc_var_prefix ^ "param___var"
  let payload_var = "v___payload"
  let env_var = "env___var"
  let app = List.filter ~f:(String.is_empty >> not) >> String.concat ~sep:" "
  let parens s = if String.contains s ' ' then "(" ^ s ^ ")" else s
end

(** Produces a method name given a dot-separated path *)
let method_name path =
  let path = String.split ~on:'.' path in
  method_prefix ^ String.concat ~sep:"__" path

(** Produces a visitor call for a type expression, without applying it. *)
let rec of_type' need_parens (t : Type.t) =
  let f =
    if String.is_prefix ~prefix:"'" t.typ then "visit_" ^ t.typ
    else "self#" ^ method_name t.typ
  in
  if List.is_empty t.args then f
  else
    app (f :: List.map ~f:(of_type' true) t.args)
    |> if need_parens then parens else Fn.id

(** Produces a complete visitor call for a type expression. *)
let of_type typ payload = app [ of_type' false typ; env_var; payload ]

let acc_var_for_field ((field, _) : Record.field) = acc_var_prefix ^ field

(** Given a list [x1; ...; xN], produces `self#plus x1 (self#plus ... (self#plus xN))` *)
let self_plus =
  List.fold_left
    ~f:(fun acc var ->
      match acc with
      | None -> Some var
      | Some acc -> Some (app [ "self#plus"; parens acc; var ]))
    ~init:None
  >> Option.value ~default:"self#zero"

(** Creates a let expression *)
let mk_let ~lhs ~rhs = "let " ^ lhs ^ " = " ^ rhs ^ " in "

let of_typed_binding ~kind (value, typ, value_binding, acc_binding) =
  let lhs =
    [
      (if is_map kind then [ value_binding ] else []);
      (if is_reduce kind then [ acc_binding ] else []);
    ]
    |> List.concat |> String.concat ~sep:", "
  in
  let rhs = of_type typ value in
  mk_let ~lhs ~rhs

let of_typed_bindings ~kind l =
  let lbs = List.map ~f:(of_typed_binding ~kind) l |> String.concat ~sep:"\n" in
  let acc = List.map ~f:(fun (_, _, _, acc) -> acc) l |> self_plus in
  (lbs, acc)

let tuple_if ~kind ?(sep = ", ") if_map if_reduce =
  [
    (if is_map kind then [ if_map ] else []);
    (if is_reduce kind then [ if_reduce ] else []);
  ]
  |> List.concat |> String.concat ~sep

let of_record ~kind ~constructor (r : Record.t) =
  let lbs, acc =
    List.map
      ~f:(fun (field, typ) ->
        (payload_var ^ "." ^ field, typ, field, acc_var_for_field (field, typ)))
      r
    |> of_typed_bindings ~kind
  in
  let record =
    constructor ^ "{" ^ String.concat ~sep:"; " (List.map ~f:fst r) ^ "}"
  in
  let result = tuple_if ~kind record acc in
  (* let result = record ^ if is_reduce kind then ", " ^ acc else "" in *)
  lbs ^ "\n" ^ result

let of_tuple_variant ~kind name (types : Type.t list) =
  let vars = List.mapi ~f:(fun i _ -> "x" ^ Int.to_string i) types in
  let accs = List.mapi ~f:(fun i _ -> "a" ^ Int.to_string i) types in
  let tuple = vars |> String.concat ~sep:", " |> parens in
  let lbs, acc =
    List.zip_exn types (List.zip_exn vars accs)
    |> List.map ~f:(fun (typ, (name, acc)) -> (name, typ, name, acc))
    |> of_typed_bindings ~kind
  in
  name ^ " " ^ tuple ^ " -> " ^ lbs ^ tuple_if ~kind (name ^ " " ^ tuple) acc

let of_variant ~kind (v : Variant.t) =
  match v.payload with
  | Tuple l -> of_tuple_variant ~kind v.name l
  | None -> v.name ^ " -> " ^ tuple_if ~kind v.name "self#zero"
  | Record record ->
      v.name ^ " " ^ payload_var ^ " -> "
      ^ of_record ~kind ~constructor:v.name record

let of_datatype ~kind (dt : Datatype.t) =
  let body =
    match dt.kind with
    | Record record -> of_record ~kind ~constructor:"" record
    | TypeSynonym typ -> of_type typ payload_var
    | Variant variants ->
        let arms =
          List.map ~f:(of_variant ~kind) variants |> String.concat ~sep:"\n  | "
        in
        "match " ^ payload_var ^ " with\n  " ^ arms
    | Opaque -> tuple_if ~kind payload_var "self#zero"
  in
  let meth = method_name dt.name in
  let self_typ =
    if Type.is_tuple_name dt.name then
      String.concat ~sep:" * " dt.type_vars |> parens
    else app [ String.concat ~sep:", " dt.type_vars |> parens; dt.name ]
  in
  let forall_clause = String.concat ~sep:" " dt.type_vars in
  let arrs =
    List.map
      ~f:(fun tvar ->
        "'env -> " ^ tvar ^ " -> "
        ^ (tuple_if ~kind ~sep:" * " tvar "'acc" |> parens))
      dt.type_vars
  in
  let arrs =
    arrs @ [ "'env"; self_typ; tuple_if ~kind ~sep:" * " self_typ "'acc" ]
  in
  let arrs = List.map ~f:parens arrs |> String.concat ~sep:" -> " in
  let meth_typ =
    List.filter ~f:(String.is_empty >> not) [ forall_clause; arrs ]
    |> String.concat ~sep:"."
  in
  let visitors =
    List.map ~f:(fun tvar -> "visit_" ^ tvar) dt.type_vars |> app
  in
  "method " ^ meth ^ " : " ^ meth_typ ^ " = fun " ^ visitors ^ " " ^ env_var
  ^ " " ^ payload_var ^ " -> " ^ body

(** Hard coded visitors *)
let extra_visitors_for = function
  | Map ->
      "        method visit_list : 'a. ('env -> 'a -> 'a) -> 'env -> 'a list \
       -> 'a list\n\
      \            =\n\
      \          fun v env -> Base.List.map ~f:(v env)\n\n"
  | MapReduce ->
      "           method visit_list\n\
      \            : 'a. ('env -> 'a -> 'a * 'acc) -> 'env -> 'a list -> 'a \
       list * 'acc\n\
      \            =\n\
      \          fun v env ->\n\
      \            Base.List.fold_map ~init:self#zero ~f:(fun acc x ->\n\
      \                let x, acc' = v env x in\n\
      \                (self#plus acc acc', x))\n\
      \            >> swap\n\n"
  | Reduce ->
      "\n\
      \          method visit_list : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a \
       list -> 'acc =\n\
      \            fun v env this ->\n\
      \              Base.List.fold ~init:self#zero\n\
      \                ~f:(fun acc -> v env >> self#plus acc)\n\
      \                this"

(** Make one kind of visitor *)
let mk_one ~kind (l : Datatype.t list) : string =
  let contents =
    List.map ~f:(of_datatype ~kind) l |> String.concat ~sep:"\n\n"
  in
  let name =
    [
      (if is_map kind then [ "map" ] else []);
      (if is_reduce kind then [ "reduce" ] else []);
    ]
    |> List.concat |> String.concat ~sep:""
  in
  let extra_visitors =
    (* visitor_for_tuples ~kind ^ "\n\n" ^ *)
    extra_visitors_for kind
  in
  "class virtual ['self] " ^ name ^ " = object (self : 'self)" ^ contents ^ "\n"
  ^ extra_visitors ^ "\nend"

(** AST.ml-specific headers *)
let header =
  "open Ast\n\
   open! Utils\n\
   open Base\n\n\
   module Make =\n\
   functor\n\
  \  (F : Features.T)\n\
  \  ->\n\
  \  struct\n\
  \    [@@@warning \"-27\"]\n\n\
  \    open Make (F)\n"

(** Only certain types should be opaque in AST.ml *)
let is_allowed_opaque name =
  let allowlist =
    [
      "Local_ident.t";
      "bool";
      "char";
      "concrete_ident";
      "global_ident";
      "attr";
      "local_ident";
      "signedness";
      "size";
      "span";
      "string";
      "todo";
      "float_kind";
      "int_kind";
      "item_quote_origin_position";
      "item_kind";
    ]
  in
  List.mem ~equal:String.equal allowlist name
  || String.is_prefix ~prefix:"F." name

(** Make all three kinds of visitors for a list of datatypes *)
let mk (l : Datatype.t list) : string =
  let l = Primitive_types.(tuples @ [ option ]) @ l in
  let opaques =
    Visitors.collect_undefined_types l
    |> List.map ~f:(fun name ->
           Datatype.{ name; type_vars = []; kind = Opaque })
  in
  (match
     Visitors.collect_undefined_types l
     |> List.filter ~f:(is_allowed_opaque >> not)
   with
  | [] -> ()
  | disallowed ->
      let msg =
        "visitor generation: forbidden opaque type: "
        ^ [%show: string list] disallowed
      in
      Stdio.prerr_endline msg;
      failwith msg);
  let l = opaques @ l in
  let visitors =
    List.map ~f:(fun kind -> mk_one ~kind l) [ Map; MapReduce; Reduce ]
  in
  let visitors = visitors |> String.concat ~sep:"\n\n" in
  [ header; visitors; "end" ] |> String.concat ~sep:"\n\n"
