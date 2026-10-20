module
public import Lean

@[expose] public section
open Lean Elab Command

/-!

# Command `open ... hiding namespace ...`

This module extends Lean's `open ... hiding ...` command with the option to provide entire
namespaces that should not be opened. The syntax is `open ... hiding namespace ...`.

The command allows us to open the `Aeneas.Std` namespace without opening `Aeneas.Std.core` and
`Aeneas.Std.alloc`. That way, we can provide our own definitions for core items.

-/

namespace CoreModels.Command

syntax (name := openHidingNs) "open" ident "hiding" "namespace" ident+ : command

@[command_elab openHidingNs]
meta def elabOpenHidingNs : CommandElab := fun stx => do
  let nsStx  : Ident                    := ⟨stx[1]⟩
  let subStxs : Array (TSyntax `ident)  := stx[4].getArgs.map (⟨·⟩)

  let ns ← resolveUniqueNamespace nsStx

  let env ← getEnv
  let exceptNames : List Name :=
    env.constants.toList.filterMap fun (nm, _) =>
      if subStxs.any (fun sub => (ns ++ sub.getId).isPrefixOf nm) then
        some (nm.replacePrefix ns .anonymous)
      else
        none

  activateScoped ns
  modifyScope fun s =>
    { s with openDecls := OpenDecl.simple ns exceptNames :: s.openDecls }

end CoreModels.Command
