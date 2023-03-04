open Base
open Utils

module type DESUGAR = sig
  val desugaring_phase : string

  module FA : Features.T
  module FB : Features.T

  module A : sig
    type item [@@deriving show]
  end

  module B : sig
    type item [@@deriving show]
  end

  val ditem : A.item -> B.item
end

module type DESUGAR_EXN = sig
  include DESUGAR

  type error [@@deriving show]

  exception Error of error
end

let _DEBUG_SHOW_ITEM = false
let _DEBUG_SHOW_BACKTRACE = false

module AddErrorHandling (D : DESUGAR) = struct
  include D

  exception DesugarError

  let ditem (i : D.A.item) : D.B.item =
    try D.ditem i
    with Failure e ->
      let desugar = List.last_exn @@ String.split ~on:'-' D.desugaring_phase in
      prerr_endline
        ("Desugaring " ^ desugar ^ " failed with exception: " ^ e ^ "\nTerm: "
        ^
        if _DEBUG_SHOW_ITEM then
          [%show: A.item] i
          ^ "\n"
          ^ if _DEBUG_SHOW_BACKTRACE then Printexc.get_backtrace () else ""
        else "");
      raise DesugarError
end

module BindDesugar
    (D1 : DESUGAR)
    (D2 : DESUGAR with module FA = D1.FB and module A = D1.B) =
struct
  module D1' = AddErrorHandling (D1)
  module D2' = AddErrorHandling (D2)
  module FA = D1.FA
  module FB = D2.FB
  module A = D1.A
  module B = D2.B

  let desugaring_phase = D1.desugaring_phase ^ "-" ^ D2.desugaring_phase
  let ditem : A.item -> B.item = D1'.ditem >> D2'.ditem
end

module CatchExnDesugar (D : DESUGAR_EXN) = struct
  include D

  let ditem (i : A.item) : B.item =
    try ditem i with D.Error error -> failwith (show_error error)
end
