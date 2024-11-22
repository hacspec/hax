module Core.Panicking
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Never = False

let never_to_any (#v_T: Type0) (x: t_Never) : v_T =
  (match x with )

let rec panic (expr: string)
    : Prims.Pure t_Never (requires false) (fun _ -> Prims.l_True) =
  panic "not yet implemented"

let panic_explicit (_: Prims.unit)
    : Prims.Pure t_Never (requires false) (fun _ -> Prims.l_True) =
  panic "not yet implemented"
