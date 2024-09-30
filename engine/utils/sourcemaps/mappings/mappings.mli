type meta = { file_offset : int; name : int option } [@@deriving show, eq]
type range = { start : Location.t; end_ : Location.t option }

module Chunk : sig
  type t = { gen : range; src : range; meta : meta } [@@deriving show, eq]

  val compare : t -> t -> int
end

open Chunk

val decode : string -> t list
val encode : t list -> string
