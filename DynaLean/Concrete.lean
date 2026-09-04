/-
Concrete bounds on the Euler iterates `S.x n`, tiers 1 and 2.

  Tier 1  `#derive_bound foo S n`            ==>  theorem foo : S.x n = v
  Tier 2  `#derive_bound foo S n digits k`   ==>  theorem foo : lo ≤ S.x n ∧ S.x n ≤ hi

Both tiers compute `S.x n` *exactly*; tier 2 only rounds the answer outward to `k`
decimal places for readability. Neither tier buys any computational headroom over
exact evaluation.

Architecture, deliberately split three ways:
  1. `evalRatCbv`  -- compute phase, untrusted, only picks the numbers.
  2. `mkBoundCmd`  -- pure syntax builder, no `MetaM`, no failure, `#eval`-testable.
  3. `elabDeriveBound` -- generate, elaborate (so the proof is *checked*), then suggest.
-/
import Mathlib
import Lean
import DynaLean.EulerScheme
set_option cbv.warning false
set_option cbv.maxSteps 10000000

open Lean Elab Command Meta
open Lean.Meta.Tactic.Cbv (cbvEntry)
open Lean.Meta.Sym.Simp (Result)
open Lean.Meta.Tactic.TryThis (addSuggestion)

/-! ## Scheme prelude

Only the parts the bound machinery needs. Replace this section with an `import` of
your own `Scheme` file and delete the duplication. -/


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
def natLitT (n : ℕ) : Term := ⟨Syntax.mkNumLit (toString n)⟩

/-- A rational literal, ascribed at `ℚ` so it does not default to `ℕ`.
Emits `(a : ℚ)`, `(-a : ℚ)`, `(a : ℚ) / b` or `(-a : ℚ) / b`. -/
def ratLit [Monad m] [MonadQuotation m] (q : ℚ) : m Term := do
  let a := natLitT q.num.natAbs
  let signed ← if q.num < 0 then `(-$a) else pure a
  if q.den == 1 then `(($signed : ℚ)) else `(($signed : ℚ) / $(natLitT q.den))

/-- The statement of the generated theorem. -/
def mkStmt [Monad m] [MonadQuotation m] (S : Term) (n : ℕ) : BoundShape → m Term
  | .eq v => do
      let xId := mkIdent `x
      `(($S).$xId $(natLitT n) = $(← ratLit v))
  | .between lo hi => do
      let xId := mkIdent `x
      let xn ← `(($S).$xId:ident $(natLitT n))
      `($(← ratLit lo) ≤ $xn ∧ $xn ≤ $(← ratLit hi))

/-- The full generated command. `prf` is the tactic chosen by the elaborator. -/
def mkBoundCmd [Monad m] [MonadQuotation m]
    (name : Ident) (S : Term) (n : ℕ) (shape : BoundShape) (prf : TSyntax `tactic) :
    m (TSyntax `command) := do
  let stmt ← mkStmt S n shape
  let declId : TSyntax ``Parser.Command.declId :=
    ⟨mkNode ``Parser.Command.declId #[name.raw, mkNullNode]⟩
  `(command| theorem $declId : $stmt := by $prf:tactic)

/-- Tier 2: round `v` outward to `digits` decimal places.
Collapses to `.eq` when `v` is exactly representable at that precision. -/
def roundTo (v : ℚ) (digits : ℕ) : BoundShape :=
  let D : ℚ := ((10 ^ digits : ℕ) : ℚ)
  let lo : ℚ := ((Rat.floor (v * D) : ℤ) : ℚ) / D
  let hi : ℚ := ((-(Rat.floor (-(v * D))) : ℤ) : ℚ) / D
  if lo == hi then .eq v else .between lo hi

/-! ## 3. Compute phase

Untrusted: it only chooses which numbers appear in the statement. A wrong answer here
cannot produce an unsound theorem, it just makes the generated proof fail loudly in
step 4. -/

private def cbvNF (e : Expr) : MetaM Expr := do
  return Result.getResultExpr e (← cbvEntry e)

/-- `getIntValue?` does not see through the raw `Int` constructors, which is what `cbv`
leaves behind for `Rat.num` (e.g. `Int.ofNat 1048576`). -/
private def intOf? (e : Expr) : MetaM (Option Int) := do
  if let some i ← getIntValue? e then return some i
  match e.getAppFnArgs with
  | (``Int.ofNat,   #[a]) => return (← getNatValue? a).map Int.ofNat
  | (``Int.negSucc, #[a]) => return (← getNatValue? a).map Int.negSucc
  | _                     => return none

/-- As `intOf?`, tolerating a raw `Nat` literal. -/
private def natOf? (e : Expr) : MetaM (Option Nat) := do
  if let some n ← getNatValue? e then return some n
  return getRawNatValue? e

/-- Reduce a closed `ℚ`-valued expression to an exact rational using `cbv`.
Falls back to reducing numerator and denominator separately, which is more robust
than hoping the normal form is a recognisable `ℚ` literal. -/
def evalRatCbv (e : Expr) : MetaM ℚ := do
  let v ← cbvNF e
  if let some q ← getRatValue? v then return q
  let numE ← cbvNF (← mkAppM ``Rat.num #[v])
  let denE ← cbvNF (← mkAppM ``Rat.den #[v])
  let some num ← intOf? numE
    | throwError "cbv did not reduce the numerator to a literal:{indentExpr numE}"
  let some den ← natOf? denE
    | throwError "cbv did not reduce the denominator to a literal:{indentExpr denE}"
  return mkRat num den


/-! ## 4. The command -/

syntax (name := deriveBoundCmd)
  "#derive_bound " ident ppSpace term:max ppSpace num (" digits " num)? : command

/-- Elaborate `cmd` speculatively; report whether it succeeded, and restore the
environment and message log either way. -/
private def cmdSucceeds (cmd : TSyntax `command) : CommandElabM Bool := do
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
private def proofCandidates : CommandElabM (Array (TSyntax `tactic)) := do
  return #[
    ← `(tactic| decide_cbv),
    ← `(tactic| norm_num [Scheme.x, Scheme.t]),
    ← `(tactic| simp [Scheme.x, Scheme.t]),
    ← `(tactic| decide)
  ]

@[command_elab deriveBoundCmd]
def elabDeriveBound : CommandElab := fun stx => do
  match stx with
  | `(command| #derive_bound $name:ident $S:term $n:num $[digits $k:num]?) => do
    let nVal := n.getNat
    -- (a) compute
    let v ← liftTermElabM do
      let eS ← Term.elabTerm S (some (mkConst ``Scheme))
      Term.synthesizeSyntheticMVarsNoPostponing
      let eS ← instantiateMVars eS
      evalRatCbv (← mkAppM ``Scheme.x #[eS, mkNatLit nVal])
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
  m := fun t x => x + t ^ 2 + x/t

/-- `δ = 1/3`, `m t x = x` ⇒ `x n = (4/3) ^ n`. Denominator `3 ^ n`: singly
exponential, so exact evaluation copes for a long time. -/
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
#derive_bound eg12 egScheme 12

-- Tier 2: outward-rounded bounds, 2 decimal places.
#derive_bound q2 qScheme 2 digits 2

-- Tier 2 on the blowup-prone scheme; raise `8` to find where exact evaluation dies.
#derive_bound sq8 sqScheme 8 digits 4
