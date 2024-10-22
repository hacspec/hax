type range = { start : Location.t; end_ : Location.t option }

module Location : sig
  type t = { line : int; col : int } [@@deriving eq]
end

type mapping = {
  gen : range;
  src : range;
  source : string;
  name : string option;
}
(** A source file to generated file mapping  *)

type t = {
  mappings : string;
  sourceRoot : string;
  sources : string list;
  sourcesContent : string option list;
  names : string list;
  version : int;
  file : string;
}
[@@deriving yojson]

val mk :
  ?file:string ->
  ?sourceRoot:string ->
  ?sourcesContent:(string -> string option) ->
  mapping list ->
  t

val to_json : t -> string
