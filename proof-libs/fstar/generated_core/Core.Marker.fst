module Core.Marker
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Copy (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self
}

class t_Destruct (v_Self: Type0) = { __marker_trait_t_Destruct:Prims.unit }

class t_Sized (v_Self: Type0) = { __marker_trait_t_Sized:Prims.unit }

class t_Tuple (v_Self: Type0) = { __marker_trait_t_Tuple:Prims.unit }
