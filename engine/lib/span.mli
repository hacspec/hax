type t [@@deriving show, yojson, sexp, compare, eq, hash]

val display : t -> string

val of_thir : Types.span -> t
(** Imports a THIR span as a hax span *)

val to_thir : t -> Types.span list
(** Exports a hax span to THIR spans (a hax span might be a collection of spans) *)

val union_list : t list -> t
val union : t -> t -> t

val dummy : unit -> t
(** Generates a dummy span: this should be avoided at all cost. *)

val id_of : t -> int
(** Lookup the internal unique identifier of a span. *)

val refresh_id : t -> t
(** Replaces the internal identifier by a fresh one. This can be useful for debugging. *)

val default : t
(** A default span can be useful when a span is required in some
computation that never reports error and when we know the span will go
away. Using this should be avoided. *)

val with_owner_hint : Types.def_id -> (unit -> 't) -> 't
(** Inserts a hint about the fact that, in function `f`, we're
translating spans that are "owned" by an item `owner`. This should be
used only in `import_thir`, also, the hint shall be used only to
enhance user reporting, not for any logic within the engine. *)

val owner_hint : t -> Types.def_id option
(** Looks up the owner hint for a span. This should be used for user
reports only. *)
