
(* module Test = struct *)
(*   module%ast Hello = functor (F: sig *)
(*                               type loop *)
(*                               type mutable_variable *)
(*                               type mutable_reference *)
(*                               type mutable_pointer *)
(*                               type mutable_borrow *)
(*                               type reference *)
(*                               type slice *)
(*                               type raw_pointer *)
(*                               type early_exit *)
(*                               type mem *)
(*                               type macro *)
(*                               type as_pattern *)
(*                               type monadic *)
(*                             end) -> struct *)
(*                        type expr *)
(*                          = MacCall of F.macro *)
(*                          | Add of (int * int * pat) *)
(*                        and pat = | Unit *)
(*                        type ('a, 'b, 'c) test = | X *)
(*                  end *)
(* end *)

(* module type X = Test.F_subtype *)
(* module Y = Test.Hello *)


module type T = sig
  type loop [@@deriving show, yojson, eq]
  type continue [@@deriving show, yojson, eq]
  type mutable_variable [@@deriving show, yojson, eq]
  type mutable_reference [@@deriving show, yojson, eq]
  type mutable_pointer [@@deriving show, yojson, eq]
  type mutable_borrow [@@deriving show, yojson, eq]
  type reference [@@deriving show, yojson, eq]
  type slice [@@deriving show, yojson, eq]
  type raw_pointer [@@deriving show, yojson, eq]
  type early_exit [@@deriving show, yojson, eq]
  type macro [@@deriving show, yojson, eq]
  type as_pattern [@@deriving show, yojson, eq]
  type lifetime [@@deriving show, yojson, eq]
  type monadic [@@deriving show, yojson, eq]
end

module SubtypeDefaults = struct
  open Base.Fn
  let loop = id
  let continue = id
  let mutable_variable = id
  let mutable_reference = id
  let mutable_pointer = id
  let mutable_borrow = id
  let reference = id
  let slice = id
  let raw_pointer = id
  let early_exit = id
  let macro = id
  let as_pattern = id
  let lifetime = id
  let monadic = id
end

module type Subtype = sig
  module A: T
  module B: T
  val loop: A.loop -> B.loop
  val continue: A.continue -> B.continue
  val mutable_variable: A.mutable_variable -> B.mutable_variable
  val mutable_reference: A.mutable_reference -> B.mutable_reference
  val mutable_pointer: A.mutable_pointer -> B.mutable_pointer
  val mutable_borrow: A.mutable_borrow -> B.mutable_borrow
  val reference: A.reference -> B.reference
  val slice: A.slice -> B.slice
  val raw_pointer: A.raw_pointer -> B.raw_pointer
  val early_exit: A.early_exit -> B.early_exit
  val macro: A.macro -> B.macro
  val as_pattern: A.as_pattern -> B.as_pattern
  val lifetime: A.lifetime -> B.lifetime
  val monadic: A.monadic -> B.monadic
end
  
type on = unit [@@deriving show, yojson, eq]
type off = | [@@deriving show, yojson, eq]

module Full = struct
  type loop = on [@@deriving show, yojson, eq]
  type continue = on [@@deriving show, yojson, eq]
  type mutable_variable = on [@@deriving show, yojson, eq]
  type mutable_reference = on [@@deriving show, yojson, eq]
  type mutable_pointer = on [@@deriving show, yojson, eq]
  type mutable_borrow = on [@@deriving show, yojson, eq]
  type reference = on [@@deriving show, yojson, eq]
  type slice = on [@@deriving show, yojson, eq]
  type raw_pointer = on [@@deriving show, yojson, eq]
  type early_exit = on [@@deriving show, yojson, eq]
  type macro = on [@@deriving show, yojson, eq]
  type as_pattern = on [@@deriving show, yojson, eq]
  type lifetime = on [@@deriving show, yojson, eq]
  type monadic = on [@@deriving show, yojson, eq]
end
  
module Rust = struct
  include Full
  type monadic = off [@@deriving show, yojson, eq]
end

(* module FStar = struct *)
(*   type loop = on [@@deriving show, yojson, eq] *)
(*   type mutable_variable = on [@@deriving show, yojson, eq] *)
      
(*   type mutable_reference = off [@@deriving show, yojson, eq] *)
(*   type mutable_pointer = off [@@deriving show, yojson, eq] *)
(*   type raw_pointer = off [@@deriving show, yojson, eq] *)
      
(*   type mutable_borrow = on [@@deriving show, yojson, eq] *)
(*   type reference = on [@@deriving show, yojson, eq] *)
(*   type slice = on [@@deriving show, yojson, eq] *)
(*   type early_exit = on [@@deriving show, yojson, eq] *)
(*   type macro = on [@@deriving show, yojson, eq] *)
(*   type as_pattern = on [@@deriving show, yojson, eq] *)
(*   type lifetime = on [@@deriving show, yojson, eq] *)
(*   type monadic = on [@@deriving show, yojson, eq] *)
(* end *)

module FStar = struct
  type loop = off [@@deriving show, yojson, eq]
  type continue = off [@@deriving show, yojson, eq]
  type mutable_variable = off [@@deriving show, yojson, eq]
  type mutable_reference = off [@@deriving show, yojson, eq]
  type mutable_pointer = off [@@deriving show, yojson, eq]
  type mutable_borrow = off [@@deriving show, yojson, eq]
  type reference = off [@@deriving show, yojson, eq]
  type slice = off [@@deriving show, yojson, eq]
  type raw_pointer = off [@@deriving show, yojson, eq]
  type early_exit = off [@@deriving show, yojson, eq]
  type macro = off [@@deriving show, yojson, eq]
  type as_pattern = off [@@deriving show, yojson, eq]
  type lifetime = off [@@deriving show, yojson, eq]
  type monadic = on [@@deriving show, yojson, eq]
end

module _ = struct
  module _: T = Full
  module _: T = Rust
  module _: T = FStar
end

