open! Prelude

type rendered = { path : string list; name : string }

module type NAME_POLICY = sig
  val reserved_words : string Hash_set.t
  (** List of all words that have a special meaning in the target
      language, and that should thus be escaped. *)

  val anonymous_field_transform : string -> string
  (** Transformation applied to anonymous tuple fields (i.e. [x.1]) *)

  val prefix_struct_constructors_with_type : bool
  val prefix_enum_constructors_with_type : bool
  val prefix_union_constructors_with_type : bool
end

module Make (T : sig
  type t
end) =
struct
  open T

  module type RENDER_API = sig
    val show : t -> string
    val pp : Formatter.t -> t -> unit
    val render : t -> rendered
    val local_ident : Local_ident.t -> string
  end
end
