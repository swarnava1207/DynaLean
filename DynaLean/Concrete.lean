module

public import Mathlib
public import Lean
public meta import DynaLean.EulerScheme
import DynaLean.EulerScheme

@[expose] public section
set_option cbv.warning false
set_option cbv.maxSteps 10000000

open Lean Elab Command Meta
open Lean.Meta.Tactic.Cbv (cbvEntry)
open Lean.Meta.Sym.Simp (Result)
open Lean.Meta.Tactic.TryThis (addSuggestion)

/-! # `#derive_bound`: concrete bounds on the Euler iterates `S.x n`

A command that evaluates a `Scheme`'s iterate `S.x n` and emits a *proved* theorem
stating the result. Two tiers:

```text
#derive_bound foo S n            ==>  theorem foo : S.x n = v
#derive_bound foo S n digits k   ==>  theorem foo : lo ≤ S.x n ∧ S.x n ≤ hi
```

Both tiers compute `S.x n` *exactly* — everything in a `Scheme` is rational. Tier 2
only rounds the answer outward to `k` decimal places so the statement is readable; it
buys no computational headroom over exact evaluation. (A hypothetical tier 3, doing a
genuine interval iteration for schemes whose denominators blow up, would slot in by
producing a `BoundShape.between` from the interval instead of from a rounded exact
value, touching nothing else in this file.)

## Architecture, deliberately split three ways

1. **Compute phase** — `unsafe evalExpr'` on `Scheme.x`. Untrusted: it only picks the
   numbers, and a wrong answer causes a failure to elaborate, not a wrong theorem.
2. **Pure syntax builders** — `natLitT`, `ratLit`, `mkStmt`, `mkBoundCmd`, `roundTo`.
   No `MetaM`, no failure modes, testable in isolation with `#eval`. This is the layer
   that stays fixed when the compute phase changes.
3. **The command** — `elabDeriveBound` generates the candidate theorem, *elaborates it*
   (via `cmdSucceeds`, so the proof is actually checked before anything is offered),
   then adds it as a `Try this` suggestion.

Nothing here is part of the trusted story: the output is an ordinary theorem whose
proof the kernel checks.
-/


/-! ## 1. What the compute phase produces

Plain data: no `Syntax`, no `Expr`. Tier 3 would slot in by producing a `.between`
from an interval iteration instead of from a rounded exact value, touching nothing else. -/

/-- The shape of the statement to emit. -/
inductive BoundShape where
  /-- The exact value is `v`. -/
  | eq (v : ℚ)
  /-- The value lies in `[lo, hi]`. -/
  | between (lo hi : ℚ)
  deriving Repr, Inhabited

/-! ## 2. Pure syntax builders

No `MetaM`, no failure modes, testable in isolation with `#eval`. This is the layer
that stays fixed when the compute phase changes. -/

/-- A `ℕ` literal as a term. -/
@[expose] public meta def natLitT (n : ℕ) : Term := ⟨Syntax.mkNumLit (toString n)⟩

/-- A rational literal, ascribed at `ℚ` so it does not default to `ℕ`.
Emits `(a : ℚ)`, `(-a : ℚ)`, `(a : ℚ) / b` or `(-a : ℚ) / b`. -/
@[expose] public meta def ratLit [Monad m] [MonadQuotation m] (q : ℚ) : m Term := do
  let a := natLitT q.num.natAbs
  let signed ← if q.num < 0 then `(-$a) else pure a
  if q.den == 1 then `(($signed : ℚ)) else `(($signed : ℚ) / $(natLitT q.den))

/-- The statement of the generated theorem. -/
@[expose] public meta def mkStmt [Monad m] [MonadQuotation m] (S : Term) (n : ℕ) : BoundShape → m Term
  | .eq v => do
      let xId := mkIdent `x
      `(($S).$xId $(natLitT n) = $(← ratLit v))
  | .between lo hi => do
      let xId := mkIdent `x
      let xn ← `(($S).$xId:ident $(natLitT n))
      `($(← ratLit lo) ≤ $xn ∧ $xn ≤ $(← ratLit hi))

/-- The full generated command. `prf` is the tactic chosen by the elaborator. -/
@[expose] public meta def mkBoundCmd [Monad m] [MonadQuotation m]
    (name : Ident) (S : Term) (n : ℕ) (shape : BoundShape) (prf : TSyntax `tactic) :
    m (TSyntax `command) := do
  let stmt ← mkStmt S n shape
  `(command| theorem $name : $stmt := by $prf:tactic)

/-- Tier 2: round `v` outward to `digits` decimal places.
Collapses to `.eq` when `v` is exactly representable at that precision. -/
@[expose] public meta def roundTo (v : ℚ) (digits : ℕ) : BoundShape :=
  let D : ℚ := ((10 ^ digits : ℕ) : ℚ)
  let lo : ℚ := ((Rat.floor (v * D) : ℤ) : ℚ) / D
  let hi : ℚ := ((-(Rat.floor (-(v * D))) : ℤ) : ℚ) / D
  if lo == hi then .eq v else .between lo hi

/-! ## 3. The command -/

/-- `#derive_bound name S n` states and proves `S.x n = v` for the exact rational `v`.

`#derive_bound name S n digits k` instead states and proves `lo ≤ S.x n ∧ S.x n ≤ hi`,
where `lo` and `hi` are `v` rounded outward to `k` decimal places.

In both cases the theorem is elaborated (hence its proof checked) before being added to
the environment, and the generated command is offered as a `Try this` suggestion so it
can be pasted into the file. Implemented by `elabDeriveBound`. -/
syntax (name := deriveBoundCmd)
  "#derive_bound " ident ppSpace term:max ppSpace num (" digits " num)? : command

/-- Elaborate `cmd` speculatively; report whether it succeeded, and restore the
environment and message log either way. -/
@[expose] public meta def cmdSucceeds (cmd : TSyntax `command) : CommandElabM Bool := do
  let saved ← get
  let ok ←
    try
      elabCommand cmd
      pure !(← get).messages.hasErrors
    catch _ => pure false
  set saved
  return ok

/-- Proof tactics tried in order. `decide_cbv` should win; the rest are insurance
against `OfNat`/instance layers that `cbv` declines to unfold. -/
@[expose] public meta def proofCandidates : CommandElabM (Array (TSyntax `tactic)) := do
  return #[
    ← `(tactic| decide_cbv),
    ← `(tactic| norm_num [Scheme.x, Scheme.t]),
    ← `(tactic| simp [Scheme.x, Scheme.t]),
    ← `(tactic| decide)
  ]

/-- The elaborator behind the `#derive_bound` command.

Runs the three phases in order: (a) evaluate `S.x n` to a `ℚ`, (b) turn the result into
a `BoundShape` and build the candidate theorem for each tactic in `proofCandidates`,
(c) keep the first candidate that really elaborates, add it to the environment, and
offer it as a `Try this` suggestion. Throws if no candidate tactic proves the computed
value. -/
@[command_elab deriveBoundCmd]
public meta def elabDeriveBound : CommandElab := fun stx => do
  match stx with
  | `(command| #derive_bound $name:ident $S:term $n:num $[digits $k:num]?) => do
    let nVal := n.getNat
    -- (a) compute
    let v ← liftTermElabM do
      let eS ← Term.elabTerm S (some (mkConst ``Scheme))
      Term.synthesizeSyntheticMVarsNoPostponing
      let eS ← instantiateMVars eS
      unsafe evalExpr' Rat ``Rat (← mkAppM ``Scheme.x #[eS, mkNatLit nVal])
    let shape := match k with
      | none    => BoundShape.eq v
      | some kk => roundTo v kk.getNat
    -- (b) build syntax, (c) check it really elaborates before offering it
    let mut chosen : Option (TSyntax `command) := none
    for tac in (← proofCandidates) do
      let cmd ← mkBoundCmd name S nVal shape tac
      if ← cmdSucceeds cmd then
        chosen := some cmd
        break
    match chosen with
    | none =>
        throwError "computed x {nVal} = {toString v}, but no candidate tactic proved it"
    | some cmd =>
        elabCommand cmd
        liftCoreM <| addSuggestion stx cmd
  | _ => throwUnsupportedSyntax


/-! ## Examples -/

/-- `δ = 1`, `m t x = x` ⇒ `x n = 2 ^ n`. Integers, exact forever. -/
def egScheme : Scheme where
  δ := 1
  hδ := by norm_num
  t₀ := 0
  x₀ := 1
  m := fun t x => x

/-- `δ = 1/3`, `m t x = x + t`, so `x (n+1) = (4/3) · x n + n / 9`. Denominators grow
like `3 ^ n`: singly exponential, so exact evaluation copes for a long time. -/
def qScheme : Scheme where
  δ := 1/3
  hδ := by norm_num
  t₀ := 0
  x₀ := 1
  m := fun t x => x + t

/-- `δ = 1/3`, `m t x = x ^ 2`. Denominators *square* each step: this is the case
that eventually forces tier 3. -/
def sqScheme : Scheme where
  δ := 1/3
  hδ := by norm_num
  t₀ := 0
  x₀ := 1
  m := fun _ x => x ^ 2

-- Tier 1: exact equality.
#derive_bound eg12 egScheme 200

-- Tier 2: outward-rounded bounds, 2 decimal places.
#derive_bound q2 qScheme 2 digits 2

-- Tier 2 on the blowup-prone scheme; raise `8` to find where exact evaluation dies.
#derive_bound sq8 sqScheme 8 digits 4
