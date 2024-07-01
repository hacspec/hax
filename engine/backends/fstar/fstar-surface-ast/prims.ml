type int = Z.t[@printer Z.pp_print][@@deriving show]
let of_int = Z.of_int
let int_zero = Z.zero
let int_one = Z.one
let parse_int = Z.of_string
let to_string = Z.to_string

type tmp = string [@@deriving yojson]
let int_to_yojson x = tmp_to_yojson (to_string x)
let int_of_yojson x =
  match tmp_of_yojson x with
  | Ok x -> Ok (parse_int x)
  | Error x -> Error x

type bool' = bool
[@@deriving yojson,show]
type bool = bool'
[@@deriving yojson,show]

type string' = string[@@deriving yojson,show]
type string = string'[@@deriving yojson,show]

let op_Negation x = not x

let ( + )     = Z.add
let ( - )     = Z.sub
let ( * )     = Z.mul
let ( / )     = Z.ediv
let ( <= )    = Z.leq
let ( >= )    = Z.geq
let ( < )     = Z.lt
let ( > )     = Z.gt
let ( mod )   = Z.erem
let ( ~- )    = Z.neg
let abs       = Z.abs

type nonrec exn = exn
let op_Hat x y = x ^ y

type 'a list' = 'a list[@@deriving yojson,show]
type 'a list = 'a list'[@@deriving yojson,show]

type nat = int
type pos = int
let string_of_bool = string_of_bool
let string_of_int = to_string
