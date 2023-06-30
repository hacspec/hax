type loc [@@deriving show, yojson, sexp, compare, eq]
type t [@@deriving show, yojson, sexp, compare, eq]

val of_thir_loc : Types.loc -> loc
val of_thir : Types.span -> t
val to_thir_loc : loc -> Types.loc
val to_thir : t -> Types.span
val union_list : t list -> t
val union : t -> t -> t
val dummy : unit -> t
val id_of : t -> int
val refresh_id : t -> t
val default : t
