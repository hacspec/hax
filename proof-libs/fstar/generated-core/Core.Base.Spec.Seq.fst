module Core.Base.Spec.Seq
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Core.Array.Rec_bundle_579704328 {t_Seq as t_Seq}

include Core.Array.Rec_bundle_579704328 {f_v as f_v}

include Core.Array.Rec_bundle_579704328 {impl as impl}

include Core.Array.Rec_bundle_579704328 {t_LIST as t_LIST}

include Core.Array.Rec_bundle_579704328 {LIST_NIL as LIST_NIL}

include Core.Array.Rec_bundle_579704328 {LIST_CONS as LIST_CONS}

include Core.Array.Rec_bundle_579704328 {nil as nil}

include Core.Array.Rec_bundle_579704328 {cons as cons}

include Core.Array.Rec_bundle_579704328 {match_list as match_list}
