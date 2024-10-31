type t [@@deriving show, yojson, sexp, compare, eq, hash]

val display : t -> string

(** Imports a THIR span as a hax span *)
val of_thir : Types.span -> t
(** Exports a hax span to THIR spans (a hax span might be a collection of spans) *)
val to_thir : t -> Types.span list

val union_list : t list -> t
val union : t -> t -> t

(** Generates a dummy span: this should be avoided at all cost. *)
val dummy : unit -> t
(** Lookup the internal unique identifier of a span. *)
val id_of : t -> int
(** Replaces the internal identifier by a fresh one. This can be useful for debugging. *)
val refresh_id : t -> t

(** A default span can be useful when a span is required in some
computation that never reports error and when we know the span will go
away. Using this should be avoided. *)
val default : t

(** Inserts a hint about the fact that, in function `f`, we're
translating spans that are "owned" by an item `owner`. This should be
used only in `import_thir`, also, the hint shall be used only to
enhance user reporting, not for any logic within the engine. *)
val with_owner_hint : Types.def_id -> (unit -> 't) -> 't

(** Looks up the owner hint for a span. This should be used for user
reports only. *)
val owner_hint: t -> Types.def_id option
