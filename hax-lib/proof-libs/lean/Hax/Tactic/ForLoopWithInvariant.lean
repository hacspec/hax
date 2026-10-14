import Hax.MissingAeneas
import CoreModels

/-! # `for_loop_with_invariant`

This file implements a tactic `for_loop_with_invariant` allows us to replace occurrences of
Aeneas's `loop` constant with a simpler construct `forLoopWithInvariant`, provided that
the original Rust loops is a for-loop. We support for-loops over any integer scalar type
(signed or unsigned) whose `Step` dictionary is recovered from the loop body, without
early returns. -/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Std.Do Elab Parser Tactic Meta
open Aeneas CoreModels
open Aeneas.Std hiding namespace core alloc
namespace Hax

/-- A `for i in s..e` loop carrying its invariant as a marker.

The argument `body : ι → β → RustM β` takes the current index and accumulator and
returns the new accumulator; `stepInst` is the `Step` dictionary of the index type `ι`.
The iterator and `ControlFlow` plumbing live entirely inside this definition. The first
argument `_inv` is a marker read off by the `for_loop_with_invariant` tactic and by
spec lemmas; it has no computational role. -/
def forLoopWithInvariant {ι β : Type} (stepInst : core.iter.range.Step ι)
    (_inv : ι → β → RustM Prop)
    (body : ι → β → RustM β)
    (rng : core.ops.range.Range ι) (init : β) :
    RustM β :=
  loop (fun x : core.ops.range.Range ι × β => do
    let (o, r) ←
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        stepInst x.1
    match o with
    | core.option.Option.None => RustM.ok (ControlFlow.done x.2)
    | core.option.Option.Some i => do
        let acc' ← body i x.2
        RustM.ok (ControlFlow.cont (r, acc'))) (rng, init)

/-! ## Body-extraction helpers (shared between the conv and regular tactics) -/

/-- Substitute every occurrence of `x.2` in `e` by `aFvar`, recognizing both
`Expr.proj Prod 1 x` and `Prod.snd _ _ x` (application) forms. -/
private def substXSnd (e : Expr) (x aFvar : Expr) : Expr :=
  e.replace fun e' =>
    match e' with
    | .proj ``Prod 1 inner => if inner == x then some aFvar else none
    | _ =>
      if e'.isAppOfArity ``Prod.snd 3 && e'.appArg! == x then some aFvar
      else none

/-- The action and continuation `(x, f)` of a monadic bind `x >>= f`, written either with the
typeclass `Bind.bind` or with `Aeneas.Std.bind`, which is what extracted code binds with. -/
private def bindParts? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Bind.bind 6 then some (e.getArg! 4, e.getArg! 5)
  else if e.isAppOfArity ``Aeneas.Std.bind 4 then some (e.getArg! 2, e.getArg! 3)
  else none

/-- Extract the user-level step body from a loop body in the precise shape
produced by Aeneas extraction (after re-associating its binds to the left with
`Aeneas.Std.bind_assoc`) for a `for i in s..e` Rust loop:
```
bind (next StepUsize x.1) <|
  Function.uncurry fun o iter1 =>
    <match>.match_1 _motive o
      (fun _ : Unit => RustM.ok (ControlFlow.done x.2))
      fun i => bind userBody fun acc' =>
        RustM.ok (ControlFlow.cont (iter1, acc'))
```
Returns `(userBody, stepDict)` with the match-bound index substituted by `jFvar`,
where `stepDict` is the `Step` dictionary taken from the loop's `next` call. -/
private def extractStepBody (jFvar : Expr) (loopBodyInner : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let inner ← whnfR loopBodyInner
  let some (nextAction, cont) := bindParts? inner | return none
  -- Recover the `Step` dictionary argument of the iterator `next` call.
  let some stepDict ← nextAction.getAppArgs.findSomeM? (fun a => do
      let t ← inferType a
      return if t.isAppOf ``core.iter.range.Step then some a else none)
    | return none
  let cont ← whnfR cont
  unless cont.isAppOfArity ``Aeneas.Std.uncurry 4 do return none
  let uncurryFn ← whnfR (cont.getArg! 3)
  unless uncurryFn.isLambda do return none
  lambdaTelescope uncurryFn fun ys matchExpr => do
    unless ys.size == 2 do return none
    let matchExpr ← whnfR matchExpr
    -- The match-aux application has shape `match_aux motive discr noneCase someCase`
    -- (4+ args). The `someCase` is the last argument and is a `fun i => ...` lambda.
    let matchArgs := matchExpr.getAppArgs
    unless matchArgs.size ≥ 4 do return none
    let someBranch ← whnfR matchArgs.back!
    unless someBranch.isLambda do return none
    lambdaTelescope someBranch fun is bodyInSome => do
      unless is.size == 1 do return none
      let i := is[0]!
      -- bodyInSome = bind userBody (fun acc' => ok (cont (iter1, acc')))
      let bodyInSome ← whnfR bodyInSome
      let some (userBody, _) := bindParts? bodyInSome | return none
      let result := userBody.replace fun e' =>
        if e' == i then some jFvar else none
      return some (result, stepDict)

/-- Recover the index type `ι` from the iterator's type, which must be
`core.ops.range.Range ι`. Throws otherwise: we only support for-loops over
ranges. -/
private def indexTypeOfIter (iter : Expr) : MetaM Expr := do
  let iterTy ← whnfR (← inferType iter)
  unless iterTy.isAppOfArity ``core.ops.range.Range 1 do
    throwError "for_loop_with_invariant: expected the iterator to have type \
      `Range _`, got{indentExpr iterTy}"
  return iterTy.getArg! 0

/-- Given a `loop B (Prod.mk _ _ iter init)` expression and an already-elaborated
invariant `inv`, build `Hax.forLoopWithInvariant inv body iter init` by extracting
`body`. Returns the new expression. Throws if the loop body doesn't have the
expected iterator/`ControlFlow.cont` shape. -/
private def buildForLoopWithInvariant
    (loopExpr inv : Expr) : MetaM Expr := do
  unless loopExpr.isAppOfArity ``Aeneas.Std.loop 4 do
    throwError "for_loop_with_invariant: expected a `loop _ _` expression"
  let initialPair := loopExpr.getArg! 3
  unless initialPair.isAppOfArity ``Prod.mk 4 do
    throwError "for_loop_with_invariant: loop's initial argument is not \
      a literal pair `(iter, init)`"
  let iter := initialPair.getArg! 2
  let init := initialPair.getArg! 3
  let elemTy ← inferType init
  let loopBody := loopExpr.getArg! 2
  let ι ← indexTypeOfIter iter
  let (stepLambda, stepDict) ← withLocalDeclD `j ι fun j =>
    withLocalDeclD `a elemTy fun a => do
      let loopBody ← whnfR loopBody
      unless loopBody.isLambda do
        throwError "for_loop_with_invariant: loop body is not a lambda"
      lambdaTelescope loopBody fun xs inner => do
        unless xs.size == 1 do
          throwError "for_loop_with_invariant: loop body has unexpected arity"
        let x := xs[0]!
        let inner := substXSnd inner x a
        let some (body, stepDict) ← extractStepBody j inner
          | throwError "for_loop_with_invariant: could not extract the loop \
              step body (expected shape \
              `bind userBody (fun acc' => ok (cont (_, acc')))`)"
        let stepLambda ← mkLambdaFVars #[j, a] body
        return (stepLambda, stepDict)
  mkAppM ``Hax.forLoopWithInvariant #[stepDict, inv, stepLambda, iter, init]

/-- Elaborate the user-supplied invariant against the expected type
`ι → β → RustM Prop`, where `β` is the element type taken from `init` and the index
type `ι` is recovered from the iterator's type `core.ops.range.Range ι`. -/
private def elabInvariant (iter init : Expr) (invStx : Term) : TacticM Expr := do
  let elemTy ← inferType init
  let ι ← indexTypeOfIter iter
  let resultProp ← mkAppM ``Aeneas.Std.RustM #[mkSort .zero]
  let invType :=
    Expr.forallE `i ι (Expr.forallE `r elemTy resultProp .default) .default
  let inv ← Term.elabTermEnsuringType invStx invType
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars inv

/-! ## Conv tactic

`conv ... => for_loop_with_invariant inv` expects the conv focus to be a
`loop _ _` expression. It normalizes the focused term with
re-associating its binds to the left, extracts the user-level step body
automatically, and rewrites the focus to
`Hax.forLoopWithInvariant inv body iter init`. -/

syntax (name := for_loop_with_invariant_conv) "for_loop_with_invariant " term : conv

@[tactic for_loop_with_invariant_conv]
def elabForLoopWithInvariantConv : Tactic := fun stx => do
  let invStx : Term := ⟨stx[1]⟩
  -- The focus is the `loop _ _` expression itself; this simp is naturally
  -- scoped to it.
  evalTactic (← `(conv|
    (try simp only [← Aeneas.Std.bind_assoc_eq, ← Aeneas.Std.bind_assoc])))
  withMainContext do
    let lhs ← instantiateMVars (← Conv.getLhs)
    let initialPair := lhs.getArg! 3
    unless initialPair.isAppOfArity ``Prod.mk 4 do
      throwError "for_loop_with_invariant: loop's initial argument is not \
        a literal pair `(iter, init)`"
    let iter := initialPair.getArg! 2
    let init := initialPair.getArg! 3
    let inv ← elabInvariant iter init invStx
    let newExpr ← buildForLoopWithInvariant lhs inv
    Conv.changeLhs newExpr

/-! ## Regular tactic

`for_loop_with_invariant inv` locates the first `loop _ _` subterm in the goal
and rewrites it to `Hax.forLoopWithInvariant inv body iter init`. It is a thin
wrapper around the conv tactic: `conv in (loop _ _) => for_loop_with_invariant inv`. -/

syntax (name := for_loop_with_invariant) "for_loop_with_invariant " term : tactic

@[tactic for_loop_with_invariant]
def elabForLoopWithInvariant : Tactic := fun stx => do
  let invStx : Term := ⟨stx[1]⟩
  evalTactic (← `(tactic|
    conv in (Aeneas.Std.loop _ _) => for_loop_with_invariant $invStx))

end Hax
