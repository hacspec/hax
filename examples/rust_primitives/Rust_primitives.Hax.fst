module Rust_primitives.Hax

type t_Never = False
let never_to_any #t: t_Never -> t = (fun _ -> match () with)
