module Core.Ops.Try_trait

class t_FromResidual self r = {
   f_from_residual: r -> self;
}

class t_Try self = {
   f_Output: Type0;
   f_Residual: Type0;
   [@@@FStar.Tactics.Typeclasses.tcresolve]
   parent_FromResidual: t_FromResidual f_Residual f_Residual;

   f_from_output: f_Output -> self;
   f_branch: self -> Core.Ops.Control_flow.t_ControlFlow f_Residual f_Output;
}


[@FStar.Tactics.Typeclasses.tcinstance]
assume val t_Try_all t: t_Try t

[@FStar.Tactics.Typeclasses.tcinstance]
assume val t_FromResidual_all t r: t_FromResidual t r
