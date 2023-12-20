open Hax_engine
open Base

let _ = Lib.main (Lib.read_options_from_stdin Yojson.Safe.from_string)
