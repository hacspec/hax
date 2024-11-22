module Core.Str.Converts
open Rust_primitives

val from_utf8 (s: t_Slice u8): Core.Result.t_Result string Core.Str.Error.t_Utf8Error

