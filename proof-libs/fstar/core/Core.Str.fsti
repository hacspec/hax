module Core.Str
open Rust_primitives

val impl__str__len: string -> usize
val impl__str__as_bytes: string -> t_Slice u8
val impl__str__contains: string FStar.Char.char -> bool

