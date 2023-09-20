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
    val dexpr : A.expr -> B.expr
  end
end

exception ReportError of Diagnostics.kind

module MakeBase
    (FA : Features.T)
    (FB : Features.T) (M : sig
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

  module Error = struct
    type t = { kind : Diagnostics.kind; span : Ast.span } [@@deriving show, eq]

    let raise err =
      let span = Span.to_thir err.span in
      Diagnostics.SpanFreeError.raise ~span (Phase M.phase_id) err.kind

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

  let export' () =
    Logs.info (fun m -> m "Exporting debug informations");
    let json =
      Hashtbl.to_alist cache
      |> List.sort ~compare:(fun (_, (a, _)) (_, (b, _)) -> Int.compare a b)
      |> List.map ~f:(fun (k, (nth, l)) ->
             let regenerate_span_ids =
               (object
                  inherit [_] Ast.Full.item_map
                  method visit_t () x = x
                  method visit_mutability _ () m = m
                  method visit_span = Fn.const Span.refresh_id
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
  let enable = Option.is_some P.metadata.previous_phase

  let ditems =
    if enable then P.ditems
    else fun items ->
      Logs.info (fun m -> m "Entering phase [%s]" name);
      let items = P.ditems items in
      Logs.info (fun m -> m "Exiting phase [%s]" name);
      items
end

module BindPhase
    (D1 : PHASE)
    (D2 : PHASE with module FA = D1.FB and module A = D1.B) =
struct
  module D1' = TracePhase (D1)
  module D2' = TracePhase (D2)
  module FA = D1.FA
  module FB = D2.FB
  module A = D1.A
  module B = D2.B

  let metadata = Metadata.bind D1.metadata D2.metadata

  let ditems (items : A.item list) : B.item list =
    let nth = List.length @@ Metadata.previous_phases D1'.metadata in
    (if Int.equal nth 0 then
     let coerce_to_full_ast : D1'.A.item -> Ast.Full.item = Stdlib.Obj.magic in
     DebugBindPhase.add Before 0 (fun _ -> List.map ~f:coerce_to_full_ast items));
    let items' = D1'.ditems items in
    let coerce_to_full_ast : D2'.A.item list -> Ast.Full.item list =
      Stdlib.Obj.magic
    in
    DebugBindPhase.add (Phase D1'.metadata.current_phase) (nth + 1) (fun _ ->
        coerce_to_full_ast items');
    D2'.ditems items'
end
