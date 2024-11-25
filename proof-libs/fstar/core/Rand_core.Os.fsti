module Rand_core.Os

type t_OsRng

[@FStar.Tactics.Typeclasses.tcinstance]
val impl_rng_core: Rand_core.t_RngCore t_OsRng

[@FStar.Tactics.Typeclasses.tcinstance]
val impl_crypto_rng_core: Rand_core.t_CryptoRngCore t_OsRng
