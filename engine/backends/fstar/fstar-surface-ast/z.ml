type t = String.t [@@deriving show]

let to_t = Base.Int.of_string
let of_t = Base.Int.to_string

let compare = String.compare
let pp_print = pp
let hash = Base.String.hash


let to_int: String.t -> Base.Int.t = Base.Int.of_string
let of_int: Base.Int.t -> String.t = Base.Int.to_string


let zero: String.t = "0"
let one: String.t = "1"
let of_string x = x
let to_string x = x

open struct
    let map (f: int -> int): string -> string = fun s -> Base.Int.of_string s |> f |> Base.Int.to_string
    let map2 (f: int -> int -> int): string -> string -> string = fun x y -> f (Base.Int.of_string x) (Base.Int.of_string y) |> Base.Int.to_string
    let map2' (f: int -> int -> 'a): string -> string -> 'a = fun x y -> f (Base.Int.of_string x) (Base.Int.of_string y)
    end

let add = map2 ( + )
let sub = map2 ( - )
let mul = map2 ( * )
let ediv = map2 ( / )
let leq = map2' ( <= )
let geq = map2' ( >= )
let lt = map2' ( < )
let gt = map2' ( > )
let erem = map2 Base.Int.( % )
let neg = map Base.Int.neg
let abs = map abs
let shift_left: string -> Base.Int.t -> string = fun x i -> Base.Int.shift_left (Base.Int.of_string x) i |> Base.Int.to_string
let shift_right: string -> Base.Int.t -> string = fun x i -> Base.Int.shift_right (Base.Int.of_string x) i |> Base.Int.to_string
