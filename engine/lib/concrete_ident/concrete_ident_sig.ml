open Base

module Make (T : sig
  type t_
  type view_
end) =
struct
  open T

  module type NAME_POLICY = sig
    val reserved_words : string Hash_set.t
    (** List of all words that have a special meaning in the target
        language, and that should thus be escaped. *)
  end

  module type VIEW_API = sig
    val show : t_ -> string
    val pp : Format.formatter -> t_ -> unit
    val to_view : t_ -> view_
    val to_definition_name : t_ -> string
    val to_crate_name : t_ -> string
    val to_namespace : t_ -> string * string list
  end
end
