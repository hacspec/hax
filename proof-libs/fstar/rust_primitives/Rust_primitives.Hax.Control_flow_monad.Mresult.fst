module Rust_primitives.Hax.Control_flow_monad.Mresult

let run (f: Core.Result.t_Result (Core.Result.t_Result 'a 'e) 'e): Core.Result.t_Result 'a 'e
    = match f with
    | Core.Result.Result_Ok x -> x 
    | Core.Result.Result_Err e -> Core.Result.Result_Err e

