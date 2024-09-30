open Prelude

type meta = { file_offset : int; name : int option } [@@deriving show, eq]
type point = Location.t Dual.t * meta option [@@deriving show, eq]
