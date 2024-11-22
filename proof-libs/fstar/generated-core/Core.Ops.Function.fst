module Core.Ops.Function
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_FnOnce (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_18093577594825678560:Core.Marker.t_Tuple v_Args;
  f_Output:Type0;
  f_call_once_pre:v_Self -> v_Args -> Type0;
  f_call_once_post:v_Self -> v_Args -> f_Output -> Type0;
  f_call_once:x0: v_Self -> x1: v_Args
    -> Prims.Pure f_Output (f_call_once_pre x0 x1) (fun result -> f_call_once_post x0 x1 result)
}

class t_FnMut (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_4383436188827019856:t_FnOnce v_Self v_Args;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_18093577594825678560:Core.Marker.t_Tuple v_Args;
  f_call_mut_pre:v_Self -> v_Args -> Type0;
  f_call_mut_post:v_Self -> v_Args -> (v_Self & _) -> Type0;
  f_call_mut:x0: v_Self -> x1: v_Args
    -> Prims.Pure (v_Self & _) (f_call_mut_pre x0 x1) (fun result -> f_call_mut_post x0 x1 result)
}

class t_Fn (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_17624495069805845666:t_FnMut v_Self v_Args;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_18093577594825678560:Core.Marker.t_Tuple v_Args;
  f_call_pre:v_Self -> v_Args -> Type0;
  f_call_post:v_Self -> v_Args -> _ -> Type0;
  f_call:x0: v_Self -> x1: v_Args
    -> Prims.Pure _ (f_call_pre x0 x1) (fun result -> f_call_post x0 x1 result)
}
