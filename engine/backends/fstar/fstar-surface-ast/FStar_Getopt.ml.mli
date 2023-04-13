val noshort : int
type 'a opt_variant =
    ZeroArgs of (unit -> 'a)
  | OneArg of (string -> 'a) * string
type 'a opt' = FStar_Char.char * string * 'a opt_variant * string
type opt = unit opt'
type parse_cmdline_res = Empty | Help | Error of string | Success
val bind :
  parse_cmdline_res -> (unit -> parse_cmdline_res) -> parse_cmdline_res
val find_matching_opt : opt list -> string -> (opt option * string) option
val parse :
  opt list ->
  (string -> parse_cmdline_res) ->
  string array -> int -> int -> int -> parse_cmdline_res
val parse_array :
  opt list ->
  (string -> parse_cmdline_res) -> string array -> int -> parse_cmdline_res
val parse_cmdline :
  opt list -> (string -> parse_cmdline_res) -> parse_cmdline_res
val parse_string :
  opt list -> (string -> parse_cmdline_res) -> string -> parse_cmdline_res
val parse_list :
  opt list ->
  (string -> parse_cmdline_res) -> string list -> parse_cmdline_res
val cmdline : unit -> string list
