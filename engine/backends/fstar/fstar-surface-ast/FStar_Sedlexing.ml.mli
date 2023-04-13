exception Error
module L = Lexing
type pos = L.position
type lexbuf = {
  buf : int array;
  len : int;
  mutable cur : int;
  mutable cur_p : pos;
  mutable start : int;
  mutable start_p : pos;
  mutable mark : int;
  mutable mark_p : pos;
  mutable mark_val : int;
}
val get_buf : lexbuf -> int array
val get_cur : lexbuf -> int
val get_start : lexbuf -> int
val create : string -> string -> int -> int -> lexbuf
val current_pos : lexbuf -> pos
val start : lexbuf -> unit
val mark : lexbuf -> int -> unit
val backtrack : lexbuf -> int
val next : lexbuf -> Uchar.t option
val new_line : lexbuf -> unit
val range : lexbuf -> pos * pos
val ulexeme : lexbuf -> int array
val rollback : lexbuf -> unit
val lexeme : lexbuf -> string
val lookahead : lexbuf -> int -> string
val source_file : lexbuf -> string
val current_line : lexbuf -> int
val __private__next_int : lexbuf -> int
