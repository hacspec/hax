module Core.Ops.Arith
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Add (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_add_pre:v_Self -> v_Rhs -> Type0;
  f_add_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_add:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result)
}

class t_Div (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_div_pre:v_Self -> v_Rhs -> Type0;
  f_div_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_div:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_div_pre x0 x1) (fun result -> f_div_post x0 x1 result)
}

class t_Mul (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_mul_pre:v_Self -> v_Rhs -> Type0;
  f_mul_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_mul:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_mul_pre x0 x1) (fun result -> f_mul_post x0 x1 result)
}

class t_Neg (v_Self: Type0) = {
  f_Output:Type0;
  f_neg_pre:v_Self -> Type0;
  f_neg_post:v_Self -> f_Output -> Type0;
  f_neg:x0: v_Self -> Prims.Pure f_Output (f_neg_pre x0) (fun result -> f_neg_post x0 result)
}

class t_Rem (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_rem_pre:v_Self -> v_Rhs -> Type0;
  f_rem_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_rem:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_rem_pre x0 x1) (fun result -> f_rem_post x0 x1 result)
}

class t_Sub (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
  f_sub_pre:v_Self -> v_Rhs -> Type0;
  f_sub_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_sub:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result)
}
