open Base
open Utils

module Metadata : sig
  type t = private {
    current_phase : Diagnostics.Phase.t;
    previous_phase : t option;
  }

  val make : Diagnostics.Phase.t -> t
  val bind : t -> t -> t
  val previous_phases : t -> Diagnostics.Phase.t list
end = struct
  type t = { current_phase : Diagnostics.Phase.t; previous_phase : t option }

  let make name = { current_phase = name; previous_phase = None }
  let bind (x : t) (y : t) : t = { y with previous_phase = Some x }

  let rec previous_phases' (p : t) : Diagnostics.Phase.t list =
    previous_phases p @ [ p.current_phase ]

  and previous_phases (p : t) : Diagnostics.Phase.t list =
    Option.map ~f:previous_phases' p.previous_phase |> Option.value ~default:[]
end

module type PHASE_ERROR = sig
  type t [@@deriving show, eq]

  val lift : t -> Diagnostics.Phase.t -> Diagnostics.t

  exception E of t
end

module DefaultError = struct
  module Error = struct
    type t = {
      kind : Diagnostics.kind;
      span : Ast.span;
    }
    [@@deriving show, eq]

    let lift { kind; span } (phase : Diagnostics.Phase.t) :
        Diagnostics.t =
      {
        kind;
        span = Diagnostics.to_thir_span span;
        context = Phase phase;
      }

    exception E of t
  end

  module _ : PHASE_ERROR = Error
end

module NoError = struct
  module Error = struct
    type t = | [@@deriving show, eq]

    let lift (x : t) (phase : Diagnostics.Phase.t) : Diagnostics.t =
      match x with _ -> .

    exception E of t
  end

  module _ : PHASE_ERROR = Error
end

module type PHASE = sig
  val metadata : Metadata.t

  module FA : Features.T
  module FB : Features.T
  module A : Ast.T
  module B : Ast.T
  module Error : PHASE_ERROR

  val ditem : A.item -> B.item list
end

module Identity (F : Features.T) = struct
  module FA = F
  module FB = F
  module A = Ast.Make (F)
  module B = Ast.Make (F)
  include NoError

  let ditem (x : A.item) : B.item list = [ Obj.magic x ]
  let metadata = Metadata.make Diagnostics.Phase.Identity
end

module _ (F : Features.T) : PHASE = Identity (F)

(* module type PHASE_EXN = sig *)
(*   include PHASE *)

(*   type error [@@deriving show] *)

(*   exception Error of error *)
(* end *)

let _DEBUG_SHOW_ITEM = false
let _DEBUG_SHOW_BACKTRACE = false

module CatchErrors (D : PHASE) = struct
  include D

  let ditem (i : D.A.item) : D.B.item list =
    try D.ditem i
    with D.Error.E e ->
      raise @@ Diagnostics.Error (D.Error.lift e D.metadata.current_phase)
end

(* TODO: This module should disappear entierly when issue #14 is
   closed (#14: Improve/add errors in simplification phases) *)
module AddErrorHandling (D : PHASE) = struct
  include D

  exception PhaseError

  let ditem (i : D.A.item) : D.B.item list =
    try D.ditem i
    with Failure e ->
      prerr_endline
        ("Phase "
        ^ [%show: Diagnostics.Phase.t] metadata.current_phase
        ^ " failed with exception: " ^ e ^ "\nTerm: "
        ^
        if _DEBUG_SHOW_ITEM then
          [%show: A.item] i
          ^ "\n"
          ^ if _DEBUG_SHOW_BACKTRACE then Printexc.get_backtrace () else ""
        else "");
      raise PhaseError
end

module DebugBindPhase : sig
  val add : Metadata.t -> (unit -> Yojson.Safe.t) -> unit
  val export : unit -> unit
end = struct
  let cache : (Diagnostics.Phase.t, int * Yojson.Safe.t list ref) Hashtbl.t =
    Hashtbl.create (module Diagnostics.Phase)

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

module BindPhase
    (D1 : PHASE)
    (D2 : PHASE with module FA = D1.FB and module A = D1.B) =
struct
  module D1' = AddErrorHandling (D1)
  module D2' = AddErrorHandling (D2)
  module FA = D1.FA
  module FB = D2.FB
  module A = D1.A
  module B = D2.B

  module Error = struct
    type t = ErrD1 of D1.Error.t | ErrD2 of D2.Error.t [@@deriving show, eq]

    let lift (x : t) (phase : Diagnostics.Phase.t) : Diagnostics.t =
      match x with
      | ErrD1 e -> D1.Error.lift e D1.metadata.current_phase
      | ErrD2 e -> D2.Error.lift e D2.metadata.current_phase

    exception E of t
  end

  module _ : PHASE_ERROR = Error

  let metadata = Metadata.bind D1.metadata D2.metadata

  let ditem : A.item -> B.item list =
   fun item0 ->
    let item1 =
      try D1'.ditem item0
      with D1.Error.E e -> raise @@ Error.E (Error.ErrD1 e)
    in
    let item2 =
      try List.concat_map ~f:D2'.ditem item1
      with D2.Error.E e -> raise @@ Error.E (Error.ErrD2 e)
    in
    DebugBindPhase.add D1.metadata (fun _ -> [%yojson_of: D1.B.item list] item1);
    item2
end
