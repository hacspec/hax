module Core.Base_interface.Int.I128_proofs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let abstract_concretize_cancel (x: Core.Base_interface.Int.t_I128)
    : Lemma Prims.l_True
      (ensures
        (Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
            #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #Core.Base_interface.Int.t_I128
                    #FStar.Tactics.Typeclasses.solve
                    x
                  <:
                  Core.Base_interface.Int.t_I128)
              <:
              Core.Base.Spec.Z.t_Z)
          <:
          Core.Base_interface.Int.t_I128) =.
        x) = ()
