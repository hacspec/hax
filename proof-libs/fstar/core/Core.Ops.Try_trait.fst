module Core.Ops.Try_trait

class t_FromResidual self r = {
   f_from_residual: r -> self;
}

class t_Try self = {
   f_Output: Type;
   f_Residual: Type;
   [@@@FStar.Tactics.Typeclasses.tcresolve]
   parent_FromResidual: t_FromResidual f_Residual f_Residual;

   f_from_output: f_Output -> self;
   f_branch: self -> Core.Ops.Control_flow.t_ControlFlow f_Residual f_Output;
}


