(* type loc [@@deriving show, yojson, sexp, compare, eq, hash] *)
type t [@@deriving show, yojson, sexp, compare, eq, hash]

val display : t -> string
val of_thir : Types.span -> t
val to_thir : t -> Types.span list
val union_list : t list -> t
val union : t -> t -> t
val dummy : unit -> t
val id_of : t -> int
val refresh_id : t -> t
val default : t
