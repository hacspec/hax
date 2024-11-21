open Prelude

type meta = { file_offset : int; name : int option }
[@@deriving show, eq, yojson]

type point = Location.t Dual.t * meta option [@@deriving show, eq, yojson]
