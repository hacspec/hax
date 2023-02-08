
module Test = struct
  module%ast Hello = functor (F: sig
                              type loop
                              type mutable_variable
                              type mutable_reference
                              type mutable_pointer
                              type mutable_borrow
                              type reference
                              type slice
                              type raw_pointer
                              type early_exit
                              type mem
                              type macro
                              type as_pattern
                              type monadic
                            end) -> struct
                       type expr
                         = MacCall of F.macro
                         | Add of (int * int * pat)
                       and pat = | Unit
                       type ('a, 'b, 'c) test = | X
                 end
end

module type X = Test.F_subtype
module Y = Test.Hello


module type T = sig
  type loop [@@deriving show, yojson, eq]
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

type on = unit [@@deriving show, yojson, eq]
type off = | [@@deriving show, yojson, eq]

module Full = struct
  type loop = on [@@deriving show, yojson, eq]
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

module FStar = struct
  type loop = off [@@deriving show, yojson, eq]
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

