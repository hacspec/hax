module Core.Iter.Adapters.Step_by
open Rust_primitives

type t_StepBy t = { 
  f_iter: t;
  f_step: n: usize {v n > 0};
  f_first_take: bool;
}

