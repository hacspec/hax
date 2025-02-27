module Core.Core_arch.X86.Sse2

val e_mm_set_epi64x: Rust_primitives.Integers.i64 -> Rust_primitives.Integers.i64 -> Core.Core_arch.X86.t_e_ee_m128i
val e_mm_cvtsi128_si32: Core.Core_arch.X86.t_e_ee_m128i -> Rust_primitives.Integers.i32
val e_mm_srli_si128: Rust_primitives.Integers.i32 -> Core.Core_arch.X86.t_e_ee_m128i -> Core.Core_arch.X86.t_e_ee_m128i