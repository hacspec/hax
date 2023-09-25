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

let apply_phases _ = failwith "xx"
let translate _ = failwith "xx"
