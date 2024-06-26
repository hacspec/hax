type 'a option' = 'a option =
  | None
  | Some of 'a[@@deriving yojson,show]

type 'a option = 'a option' =
  | None
  | Some of 'a[@@deriving yojson,show]

let fst = Stdlib.fst
let snd = Stdlib.snd
