module Hax_lib.Prop

type t_Prop = Type0

unfold let implies (lhs: t_Prop) (rhs: (x:unit{lhs} -> t_Prop)): t_Prop = (~ lhs) \/ rhs ()
