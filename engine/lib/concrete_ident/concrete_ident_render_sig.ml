open! Prelude

type rendered = { path : string list; name : string }

module type NAME_POLICY = sig
  val reserved_words : string Hash_set.t
  (** List of all words that have a special meaning in the target
      language, and that should thus be escaped. *)

  val index_field_transform : string -> string
  (** Transformation applied to indexes fields name (i.e. [x.1]) *)

  val field_name_transform : struct_name:string -> string -> string
  val enum_constructor_name_transform : enum_name:string -> string -> string
  val struct_constructor_name_transform : string -> string
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
