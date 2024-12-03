open! Prelude

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

module type PHASE = sig
  val metadata : Metadata.t

  module FA : Features.T
  module FB : Features.T
  module A : Ast.T
  module B : Ast.T

  val ditems : A.item list -> B.item list
end

module MakePhaseImplemT (A : Ast.T) (B : Ast.T) = struct
  module type T = sig
    val metadata : Metadata.t
    val ditems : A.item list -> B.item list
  end
end

(** Functor that produces module types of monomorphic phases *)
module MAKE_MONOMORPHIC_PHASE (F : Features.T) = struct
  module type ARG = sig
    val phase_id : Diagnostics.Phase.t
    val ditems : Ast.Make(F).item list -> Ast.Make(F).item list
  end

  module type T = sig
    include module type of struct
      module FB = F
      module A = Ast.Make (F)
      module B = Ast.Make (FB)
      module ImplemT = MakePhaseImplemT (A) (B)
      module FA = F
    end

    include ImplemT.T
  end
end

(** Make a monomorphic phase: a phase that transform an AST with
feature set [F] into an AST with the same feature set [F] *)
module MakeMonomorphicPhase
    (F : Features.T)
    (M : MAKE_MONOMORPHIC_PHASE(F).ARG) : MAKE_MONOMORPHIC_PHASE(F).T = struct
  module FA = F
  module FB = F
  module A = Ast.Make (F)
  module B = Ast.Make (FB)
  module ImplemT = MakePhaseImplemT (A) (B)

  module Implem = struct
    let metadata = Metadata.make M.phase_id

    include M

    let subtype (l : A.item list) : B.item list = Stdlib.Obj.magic l
    let ditems (l : A.item list) : B.item list = ditems l |> subtype
  end

  include Implem
end

(** Type of an unconstrainted (forall feature sets) monomorphic phases *)
module type UNCONSTRAINTED_MONOMORPHIC_PHASE = functor (F : Features.T) -> sig
  include module type of struct
    module FB = F
    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = MakePhaseImplemT (A) (B)
    module FA = F
  end

  include ImplemT.T
end

exception ReportError of Diagnostics.kind

module type ERROR = sig
  type t = { kind : Diagnostics.kind; span : Ast.span }

  val raise : t -> 'never
  val unimplemented : ?issue_id:int -> ?details:string -> Ast.span -> 'never
  val assertion_failure : Ast.span -> string -> 'never
end

module MakeError (Ctx : sig
  val ctx : Diagnostics.Context.t
end) : ERROR = struct
  type t = { kind : Diagnostics.kind; span : Ast.span } [@@deriving show, eq]

  let raise err =
    let span = Span.to_thir err.span in
    Diagnostics.SpanFreeError.raise ~span Ctx.ctx err.kind

  let unimplemented ?issue_id ?details span =
    raise
      {
        kind =
          Unimplemented
            { issue_id = Option.map ~f:MyInt64.of_int issue_id; details };
        span;
      }

  let assertion_failure span details =
    raise { kind = AssertionFailure { details }; span }
end

module MakeBase
    (FA : Features.T)
    (FB : Features.T)
    (M : sig
      val phase_id : Diagnostics.Phase.t
    end) =
struct
  module A = Ast.Make (FA)
  module B = Ast.Make (FB)
  module UA = Ast_utils.Make (FA)
  module UB = Ast_utils.Make (FB)
  module ImplemT = MakePhaseImplemT (A) (B)
  include M

  let metadata = Metadata.make phase_id
  let failwith = ()

  module Error : ERROR = MakeError (struct
    let ctx = Diagnostics.Context.Phase M.phase_id
  end)
end

module Identity (F : Features.T) = struct
  module FA = F
  module FB = F
  module A = Ast.Make (F)
  module B = Ast.Make (F)

  let ditems (l : A.item list) : B.item list = l
  let metadata = Metadata.make Diagnostics.Phase.Identity
end

module _ (F : Features.T) : PHASE = Identity (F)

let _DEBUG_SHOW_ITEM = false
let _DEBUG_SHOW_BACKTRACE = false

module DebugPhaseInfo = struct
  type t = Before | Phase of Diagnostics.Phase.t
  [@@deriving eq, sexp, hash, compare, yojson]

  let show (s : t) : string =
    match s with
    | Before -> "initial_input"
    | Phase p -> Diagnostics.Phase.display p

  let pp (fmt : Stdlib.Format.formatter) (s : t) : unit =
    Stdlib.Format.pp_print_string fmt @@ show s
end

module DebugBindPhase : sig
  val add : DebugPhaseInfo.t -> int -> (unit -> Ast.Full.item list) -> unit
  val export : unit -> string option
  val enable : unit -> unit
end = struct
  let enabled = ref false
  let enable () = enabled := true

  let cache : (DebugPhaseInfo.t, int * Ast.Full.item list ref) Hashtbl.t =
    Hashtbl.create (module DebugPhaseInfo)

  let add (phase_info : DebugPhaseInfo.t) (nth : int)
      (mk_item : unit -> Ast.Full.item list) =
    if !enabled (* `!` is not `not` *) then
      let _, l =
        Hashtbl.find_or_add cache phase_info ~default:(fun _ -> (nth, ref []))
      in
      l := !l @ mk_item ()
    else ()

  open struct
    module Visitors = Ast_visitors.Make (Features.Full)
  end

  let export' () =
    Logs.info (fun m -> m "Exporting debug informations");
    let json =
      Hashtbl.to_alist cache
      |> List.sort ~compare:(fun (_, (a, _)) (_, (b, _)) -> Int.compare a b)
      |> List.map ~f:(fun (k, (nth, l)) ->
             let regenerate_span_ids =
               (object
                  inherit [_] Visitors.map
                  method! visit_span = Fn.const Span.refresh_id
               end)
                 #visit_item
                 ()
             in
             (* we regenerate spans IDs, so that we have more precise regions *)
             let l = List.map ~f:regenerate_span_ids !l in
             let rustish = Print_rust.pitems l in
             let json =
               `Assoc
                 [
                   ("name", `String ([%show: DebugPhaseInfo.t] k));
                   ("nth", `Int nth);
                   ("items", [%yojson_of: Ast.Full.item list] l);
                   ( "rustish",
                     [%yojson_of: Print_rust.AnnotatedString.Output.t] rustish
                   );
                 ]
             in
             json)
    in
    `List json |> Yojson.Safe.pretty_to_string

  let export () =
    if !enabled (* recall: ! is deref, not `not`, great op. choice..... *) then
      Some (export' ())
    else None
end

module type S = sig
  module A : Ast.T

  val ditem : A.item -> Ast.Full.item list
end

module TracePhase (P : PHASE) = struct
  include P

  let name = [%show: Diagnostics.Phase.t] P.metadata.current_phase
  (* We distinguish between composite phases (i.e. `BindPhase(_)(_)`) versus non-composite ones. *)

  let composite_phase = Option.is_some P.metadata.previous_phase

  let ditems =
    if composite_phase then P.ditems
    else fun items ->
      Logs.info (fun m -> m "Entering phase [%s]" name);
      let items = P.ditems items in
      Logs.info (fun m -> m "Exiting phase [%s]" name);
      items
end

module ProfilePhase (P : PHASE) = struct
  include P

  (* We distinguish between composite phases (i.e. `BindPhase(_)(_)`) versus non-composite ones. *)
  let composite_phase = Option.is_some P.metadata.previous_phase

  let ditems items =
    if composite_phase then P.ditems items
    else
      let ctx = Diagnostics.Context.Phase P.metadata.current_phase in
      Profiling.profile ctx (List.length items) (fun () -> P.ditems items)
end

module BindPhase
    (D1 : PHASE)
    (D2 : PHASE with module FA = D1.FB and module A = D1.B) =
struct
  module D1' = ProfilePhase (TracePhase (D1))
  module D2' = ProfilePhase (TracePhase (D2))
  module FA = D1.FA
  module FB = D2.FB
  module A = D1.A
  module B = D2.B

  let metadata = Metadata.bind D1.metadata D2.metadata

  let ditems (items : A.item list) : B.item list =
    let nth = List.length @@ Metadata.previous_phases D1'.metadata in
    (if Int.equal nth 0 then
       let coerce_to_full_ast : D1'.A.item -> Ast.Full.item =
         Stdlib.Obj.magic
       in
       DebugBindPhase.add Before 0 (fun _ ->
           List.map ~f:coerce_to_full_ast items));
    let items' = D1'.ditems items in
    let coerce_to_full_ast : D2'.A.item list -> Ast.Full.item list =
      Stdlib.Obj.magic
    in
    DebugBindPhase.add (Phase D1'.metadata.current_phase) (nth + 1) (fun _ ->
        coerce_to_full_ast items');
    D2'.ditems items'
end
