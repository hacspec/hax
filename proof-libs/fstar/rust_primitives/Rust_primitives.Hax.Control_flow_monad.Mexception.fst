module Rust_primitives.Hax.Control_flow_monad.Mexception
open Core.Ops.Control_flow

let run #a: t_ControlFlow a a -> a
    = function | ControlFlow_Continue v | ControlFlow_Break v -> v


