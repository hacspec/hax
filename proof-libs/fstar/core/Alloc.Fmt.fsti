module Alloc.Fmt
open Rust_primitives

include Core.Fmt

val impl_2__new_v1 (pieces: t_Slice string) (args: Core.Fmt.Rt.t_Argument): t_Arguments
val impl_7__write_fmt (fmt: t_Formatter) (args: t_Arguments): t_Result

val format (args: t_Arguments): string



