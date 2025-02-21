module Rand_core
open Rust_primitives

class t_RngCore (t_Self: Type0) = {
  f_next_u32: t_Self -> t_Self & u32;
  f_next_u64: t_Self -> t_Self & u64;
  f_fill_bytes: t_Self -> x:t_Slice u8 -> t_Self & (y:t_Slice u8{Seq.length x == Seq.length y})
}

class t_CryptoRng (t_Self: Type0) = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  _super_core: t_RngCore t_Self;
  marker_trait: unit
}

class t_CryptoRngCore (t_Self: Type0) = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  _super_crypto: t_CryptoRng t_Self;
  f_rngcore: t_Self -> t_Self
}


