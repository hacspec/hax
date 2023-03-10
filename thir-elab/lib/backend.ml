open Utils
open Base
open Ast

module Options = struct
  type operator = string

  type t = {
    header : string;  (** a module header to inline *)
    operators : operator GlobalIdent.Map.t;
    output_directory : string;
  }
  (* [@@deriving show] *)

  let default =
    {
      header = "";
      operators = Map.empty (module GlobalIdent);
      output_directory = "out";
    }
end

module type T = sig
  module InputLanguage : Features.T
  module AST : Ast.T
  (* module DesugarToInputLanguage : Desugar_utils.DESUGAR  *)
  (* Desugar_utils.DESUGAR with module FA = Features.Rust *)
  (* and module A = Ast.Rust *)
  (* and module FB = InputLanguage *)
  (* and module B = AST *)

  module BackendOptions : sig
    type t

    val parse : t Cmdliner.Term.t
  end

  val desugar : Options.t -> BackendOptions.t -> Ast.Rust.item -> AST.item list
  val translate : Options.t -> BackendOptions.t -> AST.item list -> unit
  val name : string
end

module Registration : sig
  val register : (module T) -> unit
  val command : unit -> (Options.t -> Rust.item list -> unit) Cmdliner.Cmd.t
end = struct
  module StringHashtbl = Hashtbl.M (String)

  let backends : (module T) StringHashtbl.t = Hashtbl.create (module String)

  let register (module X : T) =
    match Hashtbl.add backends ~key:X.name ~data:(module X) with
    | `Ok -> ()
    | `Duplicate ->
        failwith @@ "Error while registrating backend [" ^ X.name
        ^ "]: a backend with a same name already exists"

  open Cmdliner

  let commands () : (Options.t -> Rust.item list -> unit) Cmd.t list =
    (* let backend_names = Hashtbl.keys backends in *)
    (* failwith @@ Stirng.concat ~sep:"," backend_names *)
    Hashtbl.to_alist backends
    |> List.map ~f:(fun (name, (module B : T)) ->
           let info = Cmd.info name in
           let opts = B.BackendOptions.parse in
           let f bo o i =
             let items = List.concat_map ~f:(B.desugar o bo) i in
             B.translate o bo items
           in
           Cmd.v info Term.(const f $ opts))

  let command () : (Options.t -> Rust.item list -> unit) Cmd.t =
    let info = Cmd.info "thir-elab" in
    Cmd.group info (commands ())
end
