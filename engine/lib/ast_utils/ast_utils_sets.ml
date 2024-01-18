open! Prelude
open Ast

module M (T : sig
  type t [@@deriving show]
  type comparator_witness

  val comparator : (t, comparator_witness) Base.Comparator.comparator
end) =
struct
  include Set.M (T)

  let show (x : t) : string = [%show: T.t list] @@ Set.to_list x

  let pp (fmt : Stdlib.Format.formatter) (s : t) : unit =
    Stdlib.Format.pp_print_string fmt @@ show s

  class ['s] monoid =
    object
      inherit ['s] VisitorsRuntime.monoid
      method private zero = Set.empty (module T)
      method private plus = Set.union
    end
end

module Global_ident = M (Global_ident)
module Concrete_ident = M (Concrete_ident)
module Local_ident = M (Local_ident)
