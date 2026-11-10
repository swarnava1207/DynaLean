module

public import Mathlib
public import Lean
public meta import Qq
public meta import DynaLean.Defs
public meta import DynaLean.EulerScheme
import DynaLean.EulerScheme

@[expose] public section
open Lean Meta Elab Term Tactic Qq
open Lean.Meta.Tactic.TryThis (addSuggestion)
open Lean Meta PrettyPrinter

/-! # Proof *building* for Euler iterates

`DynaLean.Concrete` evaluates an iterate and then searches for a tactic that can prove
the resulting equation. This module takes the opposite, and more scalable, route: it
*constructs the proof term directly*, one inference per Euler step, and never asks a
tactic to re-derive anything.

The device is an inductive predicate that mirrors the Euler recursion:

* `HasBound S n l h l₀ h₀` — starting from the interval `[l₀, h₀]` containing `S.x₀`,
  `n` Euler steps carry it to the interval `[l, h]`, which therefore contains `S.x n`
  (`hasbound_implies_bound`). Note that both ends are shifted by the *same* amount at
  each step, so the width never grows: this is an exact translation of an interval, not
  an interval-arithmetic over-approximation.
* `HasBoundVec S n c r c₀` — the `ℚ^k` analogue, phrased with a closed ball of fixed
  radius `r` whose centre is carried along by the iteration
  (`hasboundvec_implies_bound`).

On top of each predicate sit two pieces of metaprogramming:

* a tactic, `apply_bound` / `apply_bound_vec`, which closes a `HasBound(Vec)` goal by
  building the `n`-fold `.succ` chain and checking that the endpoints it reaches really
  are the ones stated in the goal (reporting both if not);
* a command, `#make_proof`, which generates and elaborates two named theorems — the
  `HasBound` statement and the membership statement it implies — and reports their
  names.

Everything here produces ordinary proof terms that the kernel checks; the `unsafe`
evaluation helpers (`RatOf`, `RatOfVec`) are only used to compare numbers for error
reporting and to decide what to build.
-/

section Scalar

/-! ## Scalar schemes -/

/-- `HasBound S n l h l₀ h₀`: `n` Euler steps of `S` carry the initial enclosure
`[l₀, h₀]` of `S.x₀` to the enclosure `[l, h]` of `S.x n`.

The two constructors mirror the recursion defining `Scheme.x`, so a proof of
`HasBound S n ...` is literally a chain of `n` applications of `succ` on top of one
`zero` — which is what `apply_bound` and `#make_proof` build. -/
inductive HasBound : Scheme → ℕ → ℚ → ℚ → ℚ → ℚ → Prop where
  /-- Zero steps: the enclosure is the initial one, witnessed by `S.x₀ ∈ [l, h]`. -/
  | zero (S : Scheme) (l h : ℚ) (hyp : S.x₀ ∈ Set.Icc l h): HasBound S 0 l h l h
  /-- One more Euler step shifts both ends of the enclosure by `δ · m (t n) (x n)`,
  leaving its width unchanged. -/
  | succ (l h l₀ h₀ : ℚ) (S : Scheme) (n : ℕ) : HasBound S n l h l₀ h₀ →
    HasBound S (n + 1) (l + S.δ * (S.m (S.t n) (S.x n))) (h + S.δ * (S.m (S.t n) (S.x n))) l₀ h₀

/-- A `HasBound` derivation really does enclose the iterate: `S.x n ∈ [l, h]`.

Proved by recursion on the derivation; the `succ` case is `add_le_add_left` applied to
the inductive hypothesis, since the step shifts the iterate and both interval ends by
the same quantity. -/
theorem hasbound_implies_bound (S : Scheme) (n : ℕ) (l h l₀ h₀ : ℚ) :
    HasBound S n l h l₀ h₀ → S.x n ∈ Set.Icc l h := fun hyp =>
  match hyp with
  | .zero S l h hyp => by simp only [Scheme.x];exact hyp
  | .succ l h l₀ h₀ S n hyp => by
    have : S.x (n + 1) = S.x n + S.δ * (S.m (S.t n) (S.x n)) := by simp only [Scheme.x]
    have h1 : l + S.δ * (S.m (S.t n) (S.x n)) ≤ S.x (n + 1) := by
      rw [this]
      exact add_le_add_left (hasbound_implies_bound S n l h l₀ h₀ hyp).1 _
    have h2 : S.x (n + 1) ≤ h + S.δ * (S.m (S.t n) (S.x n)) := by
      rw [this]
      exact add_le_add_left (hasbound_implies_bound S n l h l₀ h₀ hyp).2 _
    exact ⟨h1, h2⟩

/-- Evaluate an `Expr` of type `ℚ` to an actual `Rat`.

`unsafe` because it compiles and runs the expression; used only to compare the
endpoints a derivation reaches with the ones a goal claims, so a bad evaluation can
only produce a spurious error message, never an unsound theorem. -/
meta unsafe def RatOf (e : Expr) : MetaM Rat := evalExpr Rat (Lean.mkConst ``Rat) e

/-- Elaborate a term and fully instantiate it: `elabTerm`, then force all pending
synthetic metavariables, then `instantiateMVars`.

The combination wanted almost everywhere below, where a *closed* `Expr` is needed
rather than one still carrying unassigned metavariables. -/
meta def elab! (stx : Syntax) (ty : Option Expr := none) : TermElabM Expr := do
  let e ← elabTerm stx ty
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Build the proof term for `HasBound S n …` by chaining `n` applications of
`HasBound.succ` on top of `HasBound.zero`.

The interval endpoints are left implicit (`none` in `mkAppOptM`) so that unification
computes them from the chain itself; `hyp` is the proof — possibly still a
metavariable — that `S.x₀` lies in the initial interval. -/
meta def mkHasBoundProof (S l h l₀ h₀ hyp : Expr) : ℕ → MetaM Expr
  | 0 => mkAppM ``HasBound.zero #[S, l₀, h₀, hyp]
  | k + 1 => do
      let prev ← mkHasBoundProof S l h l₀ h₀ hyp k
      mkAppOptM ``HasBound.succ #[none, none, none, none, some S, none, some prev]


/-- Close a `HasBound S n l h l₀ h₀` goal by building the `n`-step derivation.

Reads `n` and the four endpoints off the goal, builds the chain with
`mkHasBoundProof`, and checks that the endpoints the chain actually reaches agree with
the ones in the goal — if they do not, it reports both intervals rather than failing
opaquely.

The hypothesis `S.x₀ ∈ Set.Icc l₀ h₀` is discharged from the local context if a
matching hypothesis is present; otherwise it is left as the single remaining goal. -/
elab "apply_bound" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let target ← mvarId.getType
    let args := target.getAppArgs
    unless args.size == 6 do
      throwError "apply_bound: expected 6 arguments, got {args.size}"
    unless target.getAppFn.constName! == ``HasBound do
      throwError "apply_bound: expected HasBound, got {target.getAppFn.constName!}"
    let S := args[0]!
    let n := args[1]!
    let l := args[2]!
    let h := args[3]!
    let l₀ := args[4]!
    let h₀ := args[5]!
    let nVal ← unsafe evalExpr Nat (Lean.mkConst ``Nat) n
    let iccApp ← mkAppOptM ``Set.Icc #[none, none, some l₀, some h₀]
    let hypType ← mkAppOptM ``Membership.mem #[none, none, none, some iccApp,
      some (← mkAppM ``Scheme.x₀ #[S])]
    let hyp ← mkFreshExprMVar hypType
    let pf ← mkHasBoundProof S l h l₀ h₀ hyp nVal
    let pfTy ← instantiateMVars (← inferType pf)
    let pfArgs := pfTy.getAppArgs
    let lVal := pfArgs[2]!
    let hVal := pfArgs[3]!
    let lComp ← unsafe RatOf lVal
    let hComp ← unsafe RatOf hVal
    let lWant ← unsafe RatOf l
    let hWant ← unsafe RatOf h
    unless lComp == lWant && hComp == hWant do
      throwError "apply_bound: after {nVal} step(s) the scheme reaches \
        [{lComp}, {hComp}], but the goal states [{lWant}, {hWant}]"
    mvarId.assign pf
    let hyps ← getLCtx
    let mut found := false
    for hypit in hyps do
      if hypit.isImplementationDetail then continue
      let hypTypeit ← instantiateMVars hypit.type
      if (← isDefEq hypTypeit hypType) then
        hyp.mvarId!.assign hypit.toExpr
        found := true
        break
    if ¬found then
      replaceMainGoal [hyp.mvarId!]
    else
      replaceMainGoal []

/-- `#make_proof thm₁ thm₂ S l₀ h₀ hyp n` generates and elaborates two theorems about
the scheme `S` after `n` Euler steps, given `hyp : S.x₀ ∈ Set.Icc l₀ h₀`:

* `thm₁ : HasBound S n l h l₀ h₀`, with the endpoints `l`, `h` computed by running the
  derivation; and
* `thm₂ : S.x n ∈ Set.Icc l h`, obtained from `thm₁` via `hasbound_implies_bound`.

Both statements are delaborated back to surface syntax before being elaborated, so the
theorems that enter the environment are ordinary, readable, kernel-checked ones.
Logs the two names on success. -/
elab "#make_proof" name1:ident name2:ident S:ident l₀:term:max h₀:term:max
 hyp:term:max n:num :
  command => do
  let (stx1, stx2) ← Command.liftTermElabM do
    let Se   ← elab! S
    let l₀e ← elab! l₀ (some (Lean.mkConst ``Rat))
    let h₀e ← elab! h₀ (some (Lean.mkConst ``Rat))
    let hype ← elab! hyp
    let nVal ← elabTerm n (some (Lean.mkConst ``Nat))
    let pf ← instantiateMVars (← mkHasBoundProof Se l₀e h₀e l₀e h₀e hype n.getNat)
    let ty ← instantiateMVars (← inferType pf)
    let args := ty.getAppArgs
    let lVal ← unsafe RatOf args[2]!
    let hVal ← unsafe RatOf args[3]!
    let l₀Val ← unsafe RatOf args[4]!
    let h₀Val ← unsafe RatOf args[5]!
    let prettyTy ← mkAppM ``HasBound #[Se, toExpr n.getNat, toExpr lVal, toExpr hVal,
     toExpr l₀Val, toExpr h₀Val]
    let existpf ← mkAppOptM ``hasbound_implies_bound
     #[some Se , none , none , none , none, none, some pf]
    let existpfTy ← instantiateMVars (← inferType existpf)
    let args := existpfTy.getAppArgs
    let fnname := existpfTy.getAppFn
    let val := args[3]!
    let argval := val.getAppArgs
    let argname := val.getAppFn.constName!
    let last := args[args.size - 1]!
    let lastargs := last.getAppArgs
    let lastname := last.getAppFn.constName!
    let lastargapp ← mkAppM lastname #[lastargs[0]!, nVal]
    let newargs := #[args[0]!, args[1]!, args[2]!,
      (← mkAppOptM argname #[some argval[0]!, none, some (toExpr lVal), some (toExpr hVal)]),
      lastargapp]
    let existspfPrettyTy := mkAppN fnname newargs
    let existpfPrettyTy ← PrettyPrinter.delab (← instantiateMVars existspfPrettyTy)
    let tyStx ← PrettyPrinter.delab prettyTy
    let pfStx ← PrettyPrinter.delab pf
    let stx1 ← `(command| theorem $name1 : $tyStx := by
        have hb := $pfStx
        norm_num [$S:ident, Scheme.x, Scheme.t] at hb
        exact hb)
    let stx2 ← `(command| theorem $name2 : $existpfPrettyTy := by
        have hb := $pfStx
        norm_num [$S:ident, Scheme.x, Scheme.t] at hb
        apply hasbound_implies_bound
        exact hb)
    pure (stx1, stx2)
  Command.elabCommand stx1
  Command.elabCommand stx2
  logInfo m!"Generated theorems {name1} and {name2}.
    Use `#check @{name1}` and `#check @{name2}` to see."


/-! ### Worked example

`egScheme` is `x' = x` discretized with `δ = 1` from `x₀ = 1`, so `x n = 2 ^ n`. The
`200`-step example below is the point of this module: building the derivation is linear
in the number of steps, where asking a tactic to evaluate `egScheme.x 200` from scratch
is not. -/

/-- Example scheme: `δ = 1`, `t₀ = 0`, `x₀ = 1`, `m t x = x`, so `x n = 2 ^ n`. -/
def egScheme : Scheme where
  δ := 1
  hδ := by norm_num
  t₀ := 0
  x₀ := 1
  m := fun _ x => x

/-- The initial enclosure for `egScheme`, as required by `HasBound.zero`. -/
theorem easy : egScheme.x₀ ∈ Set.Icc (-2) 1 := by norm_num; simp [egScheme]; grind

/-- The 200th iterate of `egScheme`, i.e. `2 ^ 200`, named so that `check` can state a
zero-width enclosure around it. -/
def t10 := egScheme.x 200

-- Generates `egBound : HasBound egScheme 0 1 1 1 1` and `egExists : egScheme.x 0 ∈ Set.Icc 1 1`.
#make_proof egBound egExists egScheme (1) 1 easy 0
#check @egBound
#check @egExists

/-- 200 Euler steps, proved by building the derivation rather than by evaluation:
the enclosure is the single point `t10 = egScheme.x 200`. -/
theorem check : HasBound egScheme 200 t10 t10 1 1 := by
  apply_bound
  exact easy

end Scalar

section Vector
open Metric

/-! ## Vector schemes

The same construction for `VectorScheme k`. An interval is replaced by a closed ball:
the radius `r` is fixed once and for all and only the centre moves, which is again an
exact translation rather than an over-approximation. -/

variable {k : ℕ}

/-- `HasBoundVec S n c r c₀`: `n` Euler steps of the vector scheme `S` carry the
initial ball `closedBall c₀ r` containing `S.x₀` to `closedBall c r`, which therefore
contains `S.x n`.

The `ℚ^k` analogue of `HasBound`; the radius is unchanged by a step because the step
translates both the iterate and the centre by `δ • m (t n) (x n)`. -/
inductive HasBoundVec : VectorScheme k → ℕ → (ℚ^k) → ℚ → (ℚ^k) → Prop where
  /-- Zero steps: the ball is the initial one, witnessed by `S.x₀ ∈ closedBall c r`. -/
  | zero (S : VectorScheme k) (c : ℚ^k) (r : ℚ) (hyp : S.x₀ ∈ closedBall c r) :
    HasBoundVec S 0 c r c
  /-- One more Euler step translates the centre by `δ • m (t n) (x n)` and leaves the
  radius alone. -/
  | succ (c c₀ : ℚ^k) (r : ℚ) (S : VectorScheme k) (n : ℕ) :
    HasBoundVec S n c r c₀ →
    HasBoundVec S (n + 1) (c + S.δ • (S.m (S.t n) (S.x n))) r c₀


/-- A `HasBoundVec` derivation really does enclose the iterate: `S.x n ∈ closedBall c r`.

The `ℚ^k` analogue of `hasbound_implies_bound`; the `succ` case is
`dist_add_right`, since translating both points leaves their distance unchanged. -/
theorem hasboundvec_implies_bound (S : VectorScheme k) (n : ℕ) (c c₀ : ℚ^k) (r : ℚ) :
    HasBoundVec S n c r c₀ → S.x n ∈ closedBall c r := fun hyp =>
  match hyp with
  | .zero S c r hyp => by simp only [VectorScheme.x];exact hyp
  | .succ c c₀ r S n hyp => by
    have : S.x (n + 1) = S.x n + S.δ • (S.m (S.t n) (S.x n)) := by simp only [VectorScheme.x]
    rw [this]
    simp only [mem_closedBall, dist_add_right, ge_iff_le]
    have h1 := hasboundvec_implies_bound S n c c₀ r hyp
    have h2 : dist (S.x n) c ≤ r := h1
    exact h2

/-- Transport a `HasBoundVec` derivation along an equality of centres.

Needed by `apply_bound_vec`: the centre the derivation *computes* is a nested pile of
`+` and `•`, while the centre the goal *states* is usually a normalized vector literal.
The two are equal but not syntactically so, and this lemma bridges the gap once the
equality has been proved. -/
theorem hasboundvec_congr {k : ℕ} {S : VectorScheme k} {n : ℕ} {c c' c₀ : ℚ^k} {r : ℚ}
    (h : c = c') (hb : HasBoundVec S n c r c₀) : HasBoundVec S n c' r c₀ := h ▸ hb

/-- Evaluate an `Expr` of type `ℚ^k` to an actual vector.

The `ℚ^k` analogue of `RatOf`, and used in the same way: only to compare the centre a
derivation reaches with the one a goal states. -/
meta unsafe def RatOfVec (e : Expr) : MetaM (ℚ^k) := do
    evalExpr (ℚ^k) (← mkAppM ``EuclideanSpace
        #[Lean.mkConst ``Rat, (← mkAppM ``Fin #[toExpr k])]) e

/-- Build the proof term for `HasBoundVec S n …` by chaining `n` applications of
`HasBoundVec.succ` on top of `HasBoundVec.zero`.

The `ℚ^k` analogue of `mkHasBoundProof`. -/
meta def mkHasBoundVecProof (S c r c₀ hyp : Expr) : ℕ → MetaM Expr
  | 0 => mkAppM ``HasBoundVec.zero #[S, c₀, r, hyp]
  | k + 1 => do
      let prev ← mkHasBoundVecProof S c r c₀ hyp k
      mkAppOptM ``HasBoundVec.succ #[none, none, none, none, some S, none, some prev]

/-- Close a `HasBoundVec S n c r c₀` goal by building the `n`-step derivation.

The `ℚ^k` counterpart of `apply_bound`, with one extra step. The centre reached by the
derivation and the centre written in the goal are equal but rarely syntactically
identical, so the tactic discharges the equality coordinatewise
(`ext i; fin_cases i <;> norm_num [...]`, unfolding the scheme and any local
definitions appearing in the goal) and then transports the derivation along it with
`hasboundvec_congr`.

As with `apply_bound`, the initial-ball hypothesis is taken from the local context if
present, and otherwise left as the remaining goal. Requires the scheme to be a
constant, since its name is needed among the `simp` lemmas. -/
elab "apply_bound_vec" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let target ← mvarId.getType
    let args := target.getAppArgs
    unless args.size == 6 do
      throwError "apply_bound_vec: expected 6 arguments, got {args.size}"
    unless target.getAppFn.constName! == ``HasBoundVec do
      throwError "apply_bound_vec: expected HasBoundVec, got {target.getAppFn.constName!}"
    let S := args[1]!
    let k := (← inferType args[1]!).getAppArgs[0]!
    let n := args[2]!
    let c := args[3]!
    let r := args[4]!
    let c₀ := args[5]!
    let nVal ← unsafe evalExpr Nat (Lean.mkConst ``Nat) n
    let kVal ← unsafe evalExpr Nat (Lean.mkConst ``Nat) k
    let cTarget ← unsafe RatOfVec (k := kVal) c
    let rR ← mkAppOptM ``RatCast.ratCast #[some (Lean.mkConst ``Real), none, some r]
    let iccApp ← mkAppOptM ``closedBall #[some
      (← mkAppM ``EuclideanSpace #[Lean.mkConst ``Rat , (← mkAppM ``Fin #[k])]), none,
      some c₀ , some rR]
    let hypType ← mkAppOptM ``Membership.mem #[none, none, none, some iccApp,
      some (← mkAppM ``VectorScheme.x₀ #[S])]
    let hyp ← mkFreshExprMVar hypType
    let pf ← mkHasBoundVecProof S c r c₀ hyp nVal
    let pfTy ← instantiateMVars (← inferType pf)
    let pfArgs := pfTy.getAppArgs
    let cComp := pfArgs[3]!
    let cVal ← unsafe RatOfVec (k := kVal) cComp
    unless cVal == cTarget do
      throwError "apply_bound_vec: after {nVal} step(s) the scheme reaches \
        {cComp}, but the goal states {c}"
    let some schemeName := S.constName?
      | throwError "apply_bound_vec: the scheme must be a constant, got {S}"
    let env ← getEnv
    let fromGoal := c.getUsedConstants.filter fun n =>
      !n.isInternal
        && (env.find? n matches some (.defnInfo _))
        && (env.getModuleIdxFor? n).isNone        -- i.e. defined in this file
    let unfolds := fromGoal ++ #[schemeName, ``VectorScheme.x, ``VectorScheme.t]
    let lemmas ← unfolds.mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    let eqGoal ← mkEq cComp c
    let eqPf ← elabTermAndSynthesize
      (← `(by ext i; fin_cases i <;> norm_num [$lemmas,*])) (some eqGoal)
    Term.synthesizeSyntheticMVarsNoPostponing
    let eqPf ← instantiateMVars eqPf
    if eqPf.hasSorry then
      throwError "apply_bound_vec: failed to prove equality of bounds {cComp} and {c}"
    let newpf ← mkAppM ``hasboundvec_congr #[eqPf, pf]
    mvarId.assign newpf
    let hyps ← getLCtx
    let mut found := false
    for hypit in hyps do
      if hypit.isImplementationDetail then continue
      let hypTypeit ← instantiateMVars hypit.type
      if (← isDefEq hypTypeit hypType) then
        hyp.mvarId!.assign hypit.toExpr
        found := true
        break
    if ¬found then
      replaceMainGoal [hyp.mvarId!]
    else
      replaceMainGoal []

/-! ### Worked example

The two-dimensional analogue of the scalar example: `x' = x` with `δ = 1` from
`x₀ = (1, 0)`, so `x n = (2 ^ n, 0)`. -/

/-- Example vector scheme in dimension `2`: `δ = 1`, `t₀ = 0`, `x₀ = (1, 0)`,
`m t x = x`, so `x n = (2 ^ n, 0)`. -/
def egSchemeVec : VectorScheme 2 where
  δ := 1
  hδ := by norm_num
  t₀ := 0
  x₀ := !₂[1, 0]
  m := fun _ x => x

/-- The initial enclosure for `egSchemeVec`, as required by `HasBoundVec.zero`. -/
theorem easyVec : egSchemeVec.x₀ ∈ closedBall !₂[1, 0] (1 : ℚ) := by norm_num; simp [egSchemeVec]

/-- The 20th iterate of `egSchemeVec`, i.e. `(2 ^ 20, 0)`. -/
def t10Vec := egSchemeVec.x 20
#eval t10Vec

/-- 20 Euler steps of the two-dimensional example, proved by building the derivation:
the iterate lies in the unit ball around `t10Vec`. -/
theorem checkVec :
    HasBoundVec egSchemeVec 20 t10Vec 1 !₂[1, 0] := by
  apply_bound_vec
  exact easyVec


end Vector
