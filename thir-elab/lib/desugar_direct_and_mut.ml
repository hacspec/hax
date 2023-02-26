open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
            with type raw_pointer = Features.off
             and type mutable_pointer = Features.off
             and type mutable_borrow = Features.on) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.Off.Mutable_borrow
    include Features.On.Mutable_variable
  end

  module FA = FA
  module A = Ast.Make (FA)
  module B = Ast.Make (FB)
  module S = Features.SUBTYPE.Id

  (* [%%inline_lets dmutability + dty + dborrow_kind + dpat] *)
  (* [%%inline_lets "Make.*" - dexpr] *)
end
[@@open "Subtype"]
