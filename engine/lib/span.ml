open Base
open Utils
open Ppx_yojson_conv_lib.Yojson_conv.Primitives

module FreshId = struct
  let current = ref 0

  let make () =
    let id = !current in
    current := id + 1;
    id
end

type loc = { col : int; line : int }
[@@deriving show, yojson, sexp, compare, eq]

type t =
  | Span of { file : string; hi : loc; lo : loc; id : int }
  | Dummy of { id : int }
[@@deriving show, yojson, sexp, compare, eq]

let display_loc (l : loc) : string =
  Int.to_string l.col ^ ":" ^ Int.to_string l.line

let display_span (s : t) : string =
  match s with
  | Dummy _ -> "<dummy>"
  | Span s ->
      "<" ^ s.file ^ " " ^ display_loc s.lo ^ "→" ^ display_loc s.hi ^ ">"

let show (_s : t) : string = "<span>"

let pp (fmt : Caml.Format.formatter) (s : t) : unit =
  Caml.Format.pp_print_string fmt @@ show s

let union (x : t) (y : t) : t =
  match (x, y) with
  | Dummy _, _ | _, Dummy _ -> Dummy { id = FreshId.make () }
  | Span x, Span y when String.(x.file <> y.file) ->
      failwith "TODO error: Bad span union"
  | Span { file; lo; _ }, Span { hi; _ } ->
      Span { file; lo; hi; id = FreshId.make () }

let dummy () = Dummy { id = FreshId.make () }
let default = Dummy { id = 0 }

let union_list : t list -> t =
  List.reduce ~f:union >> Option.value_or_thunk ~default:dummy

let of_thir_loc (loc : Types.loc) : loc = { col = loc.col; line = loc.line }

let of_thir (span : Types.span) : t =
  Span
    {
      lo = of_thir_loc span.lo;
      hi = of_thir_loc span.hi;
      file =
        (match span.filename with Real (LocalPath path) -> path | _ -> "?");
      id = FreshId.make ();
    }

let to_thir_loc ({ col; line } : loc) : Types.loc = { col; line }

let to_thir (s : t) : Types.span =
  match s with
  | Dummy _ ->
      let hi : Types.loc = { col = 0; line = 0 } in
      { filename = Custom "DUNMMY"; hi; lo = hi }
  | Span { file; hi; lo; _ } ->
      {
        filename = Real (LocalPath file);
        hi = to_thir_loc hi;
        lo = to_thir_loc lo;
      }

let id_of = function Span { id; _ } | Dummy { id } -> id

let refresh_id span =
  let id = FreshId.make () in
  match span with Dummy _ -> Dummy { id } | Span s -> Span { s with id }
