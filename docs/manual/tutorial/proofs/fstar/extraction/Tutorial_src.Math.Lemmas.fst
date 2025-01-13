module Tutorial_src.Math.Lemmas
#set-options "--fuel 0 --ifuel 1 --z3rlimit 150"
open Core
open FStar.Mul


val cancel_mul_mod (a:i32) (n:i32 {v n >= 0}) : Lemma ((v a * v n) % v n == 0)
let cancel_mul_mod a n =
  FStar.Math.Lemmas.cancel_mul_mod (v a) (v n)
