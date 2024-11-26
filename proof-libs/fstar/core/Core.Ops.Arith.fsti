module Core.Ops.Arith
open Rust_primitives


class t_Add self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_add_pre: self -> rhs -> bool;
   f_add_post: self -> rhs -> f_Output -> bool;
   f_add: x:self -> y:rhs -> Pure f_Output (f_add_pre x y) (fun r -> f_add_post x y r);
}

class t_Sub self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_sub_pre: self -> rhs -> bool;
   f_sub_post: self -> rhs -> f_Output -> bool;
   f_sub: x:self -> y:rhs -> Pure f_Output (f_sub_pre x y) (fun r -> f_sub_post x y r);
}

class t_Mul self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_mul_pre: self -> rhs -> bool;
   f_mul_post: self -> rhs -> f_Output -> bool;
   f_mul: x:self -> y:rhs -> Pure f_Output (f_mul_pre x y) (fun r -> f_mul_post x y r);
}

class t_Div self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_div_pre: self -> rhs -> bool;
   f_div_post: self -> rhs -> f_Output -> bool;
   f_div: x:self -> y:rhs -> Pure f_Output (f_div_pre x y) (fun r -> f_div_post x y r);
}

class t_AddAssign self rhs = {
  f_add_assign_pre: self -> rhs -> bool;
  f_add_assign_post: self -> rhs -> self -> bool;
  f_add_assign: x:self -> y:rhs -> Pure self (f_add_assign_pre x y) (fun r -> f_add_assign_post x y r);
}

class t_SubAssign self rhs = {
  f_sub_assign_pre: self -> rhs -> bool;
  f_sub_assign_post: self -> rhs -> self -> bool;
  f_sub_assign: x:self -> y:rhs -> Pure self (f_sub_assign_pre x y) (fun r -> f_sub_assign_post x y r);
}

