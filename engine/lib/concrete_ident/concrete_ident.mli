type t [@@deriving show, yojson, compare, sexp, eq]

val crate : t -> string
val path : t -> string Non_empty_list.t

type name = Concrete_ident_generated.name

val of_def_id : Types.def_id -> t
val of_name : name -> t
val eq_name : name -> t -> bool

(* (\* Rust's [core] names we produce *\) *)
(* module Core : sig *)
(*   module Result : sig *)
(*     val ok : t *)
(*     val some : t *)
(*   end *)

(*   module Iter : sig *)
(*     module Iterator : sig *)
(*       val fold : t *)
(*     end *)
(*   end *)

(*   module Ops : sig *)
(*     module ControlFlow : sig *)
(*       val continue : t *)
(*       val break : t *)
(*     end *)

(*     module Index : sig *)
(*       val index : t *)
(*     end *)

(*     module FromResidual : sig *)
(*       val from_residual : t *)
(*     end *)
(*   end *)
(* end *)

(* (\* Extra definitions (i.e. non Rust core) we introduce with Hax *\) *)
(* module Hax : sig *)
(*   module Error : sig *)
(*     val failure : t *)
(*   end *)

(*   module Array : sig *)
(*     val repeat : t *)
(*     val update_at : t *)
(*   end *)

(*   module CoerceUnsize : sig *)
(*     val unsize : t *)
(*   end *)

(*   module MonadicCf : sig *)
(*     val lift : t *)
(*     val mexception : t *)
(*   end *)
(* end *)
