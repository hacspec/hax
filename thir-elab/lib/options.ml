open Base
open Utils
open Ast
open Cmdliner

(* let count = *)
(*   let doc = "Repeat the message $(docv) times." in *)
(*   Arg.(value & opt int 10 & info [ "c"; "count" ] ~docv:"COUNT" ~doc) *)

(* let chorus_t = Term.(const Fn.id $ count) *)

(* let global_ident_cmdliner_converter = *)
(*   (, fun fmt t -> Format.fprintf fmt "%s" (to_string t)) *)

type t = {
  output_directory : string;
  name_remapping : (GlobalIdent.t * GlobalIdent.t) list;
  binary_operators : (GlobalIdent.t * string) list;
}
[@@deriving cmdliner, show]

let main () =
  let f p = show p |> print_endline in
  let info = Cmdliner.Cmd.info Sys.argv.(0) in
  let term = Cmdliner.Term.(const f $ cmdliner_term ()) in
  let cmd = Cmdliner.Cmd.v info term in
  exit (Cmdliner.Cmd.eval cmd)
