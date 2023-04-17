open Base
open Utils

module Metadata : sig
  type t = private { current_phase : string; previous_phase : t option }

  val make : string -> t
  val bind : t -> t -> t
  val previous_phases : t -> string list
end = struct
  type t = { current_phase : string; previous_phase : t option }

  let make name = { current_phase = name; previous_phase = None }
  let bind (x : t) (y : t) : t = { y with previous_phase = Some x }

  let rec previous_phases' (p : t) : string list =
    previous_phases p @ [ p.current_phase ]

  and previous_phases (p : t) : string list =
    Option.map ~f:previous_phases' p.previous_phase |> Option.value ~default:[]
end

module type DESUGAR = sig
  val metadata : Metadata.t

  module FA : Features.T
  module FB : Features.T
  module A : Ast.T
  module B : Ast.T

  val ditem : A.item -> B.item list
end

module Identity (F : Features.T) = struct
  module FA = F
  module FB = F
  module A = Ast.Make (F)
  module B = Ast.Make (F)

  let ditem (x : A.item) : B.item list = [ Obj.magic x ]
  let metadata = Metadata.make "Identity"
end

module _ (F : Features.T) : DESUGAR = Identity (F)

module type DESUGAR_EXN = sig
  include DESUGAR

  type error [@@deriving show]

  exception Error of error
end

let _DEBUG_SHOW_ITEM = false
let _DEBUG_SHOW_BACKTRACE = false

module AddErrorHandling (D : DESUGAR) = struct
  include D

  exception DesugarError

  let ditem (i : D.A.item) : D.B.item list =
    try D.ditem i
    with Failure e ->
      prerr_endline
        ("Desugaring " ^ metadata.current_phase ^ " failed with exception: " ^ e
       ^ "\nTerm: "
        ^
        if _DEBUG_SHOW_ITEM then
          [%show: A.item] i
          ^ "\n"
          ^ if _DEBUG_SHOW_BACKTRACE then Printexc.get_backtrace () else ""
        else "");
      raise DesugarError
end

module DebugBindDesugar : sig
  val add : Metadata.t -> (unit -> Yojson.Safe.t) -> unit
  val export : unit -> unit
end = struct
  let cache : (string, int * Yojson.Safe.t list ref) Hashtbl.t =
    Hashtbl.create (module String)

  let add (phase_name : Metadata.t) (mk_json : unit -> Yojson.Safe.t) =
    let _, l =
      Hashtbl.find_or_add cache phase_name.current_phase ~default:(fun _ ->
          (List.length @@ Metadata.previous_phases phase_name, ref []))
    in
    l := !l @ [ mk_json () ]

  let export () =
    let all =
      Hashtbl.to_alist cache
      |> List.sort ~compare:(fun (_, (a, _)) (_, (b, _)) -> Int.compare a b)
      |> List.map ~f:(fun (k, (nth, l)) ->
             `Assoc
               [ ("name", `String k); ("nth", `Int nth); ("items", `List !l) ])
    in
    (* Core_kernel.Out_channel.write_all ~data:(`List all |> Yojson.Safe.pretty_to_string) *)
    (* @@ "/tmp/debug-circus-engine.json" *)
    ()
end

module BindDesugar
    (D1 : DESUGAR)
    (D2 : DESUGAR with module FA = D1.FB and module A = D1.B) =
struct
  module D1' = AddErrorHandling (D1)
  module D2' = AddErrorHandling (D2)
  module FA = D1.FA
  module FB = D2.FB
  module A = D1.A
  module B = D2.B

  let metadata = Metadata.bind D1.metadata D2.metadata

  let ditem : A.item -> B.item list =
   fun item0 ->
    let item1 = D1'.ditem item0 in
    let item2 = List.concat_map ~f:D2'.ditem item1 in
    DebugBindDesugar.add D1.metadata (fun _ ->
        [%yojson_of: D1.B.item list] item1);
    item2
end

module CatchExnDesugar (D : DESUGAR_EXN) = struct
  include D

  let ditem (i : A.item) : B.item list =
    try ditem i with D.Error error -> failwith (show_error error)
end
