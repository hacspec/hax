module Core.Ops.Deref

class t_Deref (t_Self: Type0) = {
   f_Target: Type0;
   f_deref: t_Self -> f_Target;
}

unfold
instance identity_Deref t_Self: t_Deref t_Self = {
  f_Target = t_Self;
  f_deref = (fun x -> x);
}
