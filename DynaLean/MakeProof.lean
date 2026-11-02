module

public import Mathlib
public import Lean
public meta import Qq
public meta import DynaLean.EulerScheme
import DynaLean.EulerScheme

@[expose] public section
open Lean Meta Elab Term Tactic Qq
open Lean.Meta.Tactic.TryThis (addSuggestion)
open Lean Meta PrettyPrinter

namespace Actual

inductive HasBound : Scheme → ℕ → ℚ → ℚ → ℚ → ℚ → Prop where
  | zero (S : Scheme) (l h : ℚ) (hyp : S.x₀ ∈ Set.Icc l h): HasBound S 0 l h l h
  | succ (l h l₀ h₀ : ℚ) (S : Scheme) (n : ℕ) : HasBound S n l h l₀ h₀ →
    HasBound S (n + 1) (l + S.δ * (S.m (S.t n) (S.x n))) (h + S.δ * (S.m (S.t n) (S.x n))) l₀ h₀

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

meta unsafe def RatOf (e : Expr) : MetaM Rat := evalExpr Rat (Lean.mkConst ``Rat) e

meta def elab! (stx : Syntax) (ty : Option Expr := none) : TermElabM Expr := do
  let e ← elabTerm stx ty
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

meta def mkHasBoundProof (S l h l₀ h₀ hyp : Expr) : ℕ → MetaM Expr
  | 0 => mkAppM ``HasBound.zero #[S, l₀, h₀, hyp]
  | k + 1 => do
      let prev ← mkHasBoundProof S l h l₀ h₀ hyp k
      mkAppOptM ``HasBound.succ #[none, none, none, none, some S, none, some prev]


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


def egScheme : Scheme where
  δ := 1
  hδ := by norm_num
  t₀ := 0
  x₀ := 1
  m := fun _ x => x

theorem easy : egScheme.x₀ ∈ Set.Icc (-2) 1 := by norm_num; simp [egScheme]; grind

def t10 := egScheme.x 200

#make_proof egBound egExists egScheme (1) 1 easy 0
#check @egBound
#check @egExists

theorem check (e : egScheme.x₀ ∈ Set.Icc 0 1) : HasBound egScheme 200 t10 t10 1 1 := by
  apply_bound

end Actual
