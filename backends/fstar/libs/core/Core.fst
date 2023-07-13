module Core

open FStar.SizeT

let usize = t
let (%.) = rem
let (=.): (#t:eqtype) -> t -> t -> bool = (=)
let (~.): bool -> bool = not
