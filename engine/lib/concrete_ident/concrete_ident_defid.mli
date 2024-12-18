type kind = Regular | StructConstructor
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

type t [@@deriving show, yojson, hash, compare, sexp, hash, eq]

val parent : t -> t option
val parents : t -> t list
val make : kind -> Types.def_id -> t
val def_id : t -> Types.def_id_contents
val kind : t -> kind
val list_all : unit -> t list
