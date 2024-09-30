open! Prelude
open! Ast

include module type of struct
  (** Protects some methods from being called or overrided. *)
  module SecretTypes = struct
    type 't no_override = private 't
    (** Hello *)

    type 'location no_direct_call = private unit
    (** Hello *)
  end

  include Generic_printer_base_sig.Types
end

val ( !: ) : 'a. 'a SecretTypes.no_override -> 'a

module Make (F : Features.T) : sig
  open Generic_printer_base_sig.Make(F)(SecretTypes)

  class virtual base : print_base_type
end
