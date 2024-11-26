module Core.Ops.Control_flow

type t_ControlFlow (b c: Type) = 
  | ControlFlow_Continue of c
  | ControlFlow_Break of b

