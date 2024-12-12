module Core.Result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Result (v_T: Type0) (v_E: Type0) =
  | Result_Ok : v_T -> t_Result v_T v_E
  | Result_Err : v_E -> t_Result v_T v_E

let impl__ok (#v_T #v_E: Type0) (self: t_Result v_T v_E) : Core.Option.t_Option v_T =
  match self with
  | Result_Ok x -> Core.Option.Option_Some x <: Core.Option.t_Option v_T
  | Result_Err _ -> Core.Option.Option_None <: Core.Option.t_Option v_T
