module Rand_core
open Rust_primitives

class t_RngCore (t_Self: Type0) = {
  f_next_u32: t_Self -> t_Self & u32;
  f_next_u64: t_Self -> t_Self & u64;
  f_fill_bytes: t_Self -> t_Slice u8 -> t_Self & t_Slice u8
}

class t_CryptoRng (t_Self: Type0) = {
  marker_trait: unit
}
