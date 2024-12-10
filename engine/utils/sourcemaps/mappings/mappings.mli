type meta = { file_offset : int; name : int option }
[@@deriving show, eq, yojson]

type range = { start : Location.t; end_ : Location.t option }
[@@deriving show, eq, yojson]

module Chunk : sig
  type t = { gen : range; src : range; meta : meta }
  [@@deriving show, eq, yojson]

  val compare : t -> t -> int
end

open Chunk

val decode : string -> t list
val encode : t list -> string
