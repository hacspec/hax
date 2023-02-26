open Subtype

(* module Detect (F: Features.T) = struct *)
(*   open Ast *)

(*   module S = struct *)
(*     module A = F *)
(*     module B = F *)
(*     let loop = id *)
(*     let continue = id *)
(*     let mutable_variable = id *)
(*     let mutable_reference = id *)
(*     let mutable_pointer = id *)
(*     let mutable_borrow = id *)
(*     let reference = id *)
(*     let slice = id *)
(*     let raw_pointer = id *)
(*     let early_exit = id *)
(*     let macro = id *)
(*     let as_pattern = id *)
(*     let lifetime = id *)
(*     let monadic = id *)
(*   end *)

(*   (\* include Subtype.Make(S) *\) *)
(*   include Subtype.Make(F)(F)(S) *)

(* end *)

(*   module MakeContinueReject (FA : Features.T) = struct *)

(*   module S = struct *)
(*     module A = FA *)
(*     module B = FB *)
(*     include Features.SUBTYPE.Id *)
(*     let continue _ = failwith "continue" *)
(*   end *)

(*   (\* include Subtype.Make(S) *\) *)
(*   include Subtype.Make(FA)(FB)(S) *)
(* end *)
