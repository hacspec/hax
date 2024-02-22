open Hax_engine

include
  Backend.Make
    (struct
      open Features
      include Off
    end)
    (struct
      let backend = Diagnostics.Backend.Scheme
    end)

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions

let apply_phases (bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  []

let translate m (bo : BackendOptions.t) (items : AST.item list) :
    Types.file list =
  []
