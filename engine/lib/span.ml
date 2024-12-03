open! Prelude

module FreshId = struct
  let current = ref 1

  let make () =
    let id = !current in
    current := id + 1;
    id
end

module Imported = struct
  type span = { filename : file_name; hi : loc; lo : loc }
  and loc = { col : int; line : int }

  and file_name =
    | Real of real_file_name
    | QuoteExpansion of string
    | Anon of string
    | MacroExpansion of string
    | ProcMacroSourceCode of string
    | CliCrateAttr of string
    | Custom of string
    | DocTest of string
    | InlineAsm of string

  and real_file_name =
    | LocalPath of string
    | Remapped of { local_path : string option; virtual_name : string }
  [@@deriving show, yojson, sexp, compare, eq, hash]

  let file_name_of_thir : Types.file_name -> file_name = function
    | Real x ->
        Real
          (match x with
          | LocalPath x -> LocalPath x
          | Remapped { local_path; virtual_name } ->
              Remapped { local_path; virtual_name })
    | QuoteExpansion x -> QuoteExpansion x
    | Anon x -> Anon x
    | MacroExpansion x -> MacroExpansion x
    | ProcMacroSourceCode x -> ProcMacroSourceCode x
    | CliCrateAttr x -> CliCrateAttr x
    | Custom x -> Custom x
    | DocTest x -> DocTest x
    | InlineAsm x -> InlineAsm x

  let loc_of_thir ({ col; line } : Types.loc) : loc =
    { col = Int.of_string col; line = Int.of_string line }

  let span_of_thir (s : Types.span) : span =
    {
      filename = file_name_of_thir s.filename;
      hi = loc_of_thir s.hi;
      lo = loc_of_thir s.lo;
    }

  let file_name_to_thir : file_name -> Types.file_name = function
    | Real x ->
        Real
          (match x with
          | LocalPath x -> LocalPath x
          | Remapped { local_path; virtual_name } ->
              Remapped { local_path; virtual_name })
    | QuoteExpansion x -> QuoteExpansion x
    | Anon x -> Anon x
    | MacroExpansion x -> MacroExpansion x
    | ProcMacroSourceCode x -> ProcMacroSourceCode x
    | CliCrateAttr x -> CliCrateAttr x
    | Custom x -> Custom x
    | DocTest x -> DocTest x
    | InlineAsm x -> InlineAsm x

  let loc_to_thir ({ col; line } : loc) : Types.loc =
    { col = Int.to_string col; line = Int.to_string line }

  let span_to_thir (s : span) : Types.span =
    {
      filename = file_name_to_thir s.filename;
      hi = loc_to_thir s.hi;
      lo = loc_to_thir s.lo;
    }

  let display_loc (l : loc) : string =
    Int.to_string l.col ^ ":" ^ Int.to_string l.line

  let display_span (s : span) : string =
    let file =
      match s.filename with
      | Real (LocalPath path) -> path
      | s -> [%show: file_name] s
    in
    "<" ^ file ^ " " ^ display_loc s.lo ^ "→" ^ display_loc s.hi ^ ">"
end

type owner_id = OwnerId of int
[@@deriving show, yojson, sexp, compare, eq, hash]

let owner_id_list = ref []

let fresh_owner_id (owner : Types.def_id) : owner_id =
  let next_id = OwnerId (List.length !owner_id_list) in
  owner_id_list := owner :: !owner_id_list;
  next_id

(** This state changes the behavior of `of_thir`: the hint placed into
this state will be inserted automatically by `of_thir`. The field
`owner_hint` shall be used solely for reporting to the user, not for
any logic within the engine. *)
let state_owner_hint : owner_id option ref = ref None

let with_owner_hint (type t) (owner : Types.def_id) (f : unit -> t) : t =
  let previous = !state_owner_hint in
  state_owner_hint := Some (fresh_owner_id owner);
  let result = f () in
  state_owner_hint := previous;
  result

type t = { id : int; data : Imported.span list; owner_hint : owner_id option }
[@@deriving show, yojson, sexp, compare, eq, hash]

let display { id = _; data; _ } =
  match data with
  | [] -> "<dummy>"
  | [ span ] -> Imported.display_span span
  | spans -> List.map ~f:Imported.display_span spans |> String.concat ~sep:"∪"

let of_thir span =
  {
    data = [ Imported.span_of_thir span ];
    id = FreshId.make ();
    owner_hint = !state_owner_hint;
  }

let to_thir { data; _ } = List.map ~f:Imported.span_to_thir data

let union_list spans =
  let data = List.concat_map ~f:(fun { data; _ } -> data) spans in
  let owner_hint = List.hd spans |> Option.bind ~f:(fun s -> s.owner_hint) in
  { data; id = FreshId.make (); owner_hint }

let union x y = union_list [ x; y ]

let dummy () =
  { id = FreshId.make (); data = []; owner_hint = !state_owner_hint }

let id_of { id; _ } = id
let refresh_id span = { span with id = FreshId.make () }
let default = { id = 0; data = []; owner_hint = None }

let owner_hint span =
  span.owner_hint
  |> Option.bind ~f:(fun (OwnerId id) -> List.nth !owner_id_list id)
