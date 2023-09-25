(* -------------------------------------------------------------------- *)
open Hax_engine
open Utils
open Base

(* -------------------------------------------------------------------- *)

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Monadic_binding
      include On.Slice
      include On.Macro
      include On.Construct_base
    end)
    (struct
      let backend = Diagnostics.Backend.Lean
    end)

module BackendOptions = Backend.UnitBackendOptions
module AST = Ast.Make (InputLanguage)

let apply_phases (_opts: BackendOptions.t) (items: Ast.Rust.item list) = []

let translate (_opts: BackendOptions.t) (items: AST.item list) = []
