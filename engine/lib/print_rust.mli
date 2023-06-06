open Ast.Full

module AnnotatedString : sig
  module Output : sig
    type t [@@deriving show, yojson]

    val raw_string : t -> string
  end
end

val pitem : item -> AnnotatedString.Output.t
val pitem_str : item -> string
val pexpr_str : expr -> string
