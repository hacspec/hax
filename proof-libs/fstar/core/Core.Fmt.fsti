module Core.Fmt
open Rust_primitives

val t_Error: Type0

type t_Result = Core.Result.t_Result unit t_Error

val t_Formatter: Type0
class t_Display #t_Self = {
  f_fmt_pre: t_Self -> Core.Fmt.t_Formatter -> bool;
  f_fmt_post: t_Self -> Core.Fmt.t_Formatter -> (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) -> bool;
  f_fmt: t_Self -> Core.Fmt.t_Formatter -> (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
}

val t_Arguments: Type0
val impl_2__new_v1 (pieces: t_Slice string) (args: t_Slice Core.Fmt.Rt.t_Argument): t_Arguments
val impl_7__write_fmt (fmt: t_Formatter) (args: t_Arguments): t_Formatter & t_Result
val impl_2__new_const (args: t_Slice string): t_Arguments

