module Rust_primitives.Hax.Control_flow_monad.Moption

let run (f: Core.Option.t_Option (Core.Option.t_Option 'a)): Core.Option.t_Option 'a
    = match f with
    | Core.Option.Option_Some x -> x 
    | Core.Option.Option_None -> Core.Option.Option_None

