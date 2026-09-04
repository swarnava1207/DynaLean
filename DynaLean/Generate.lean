import DynaLean.EulerScheme
import Lean
open Lean Elab Command Term Meta PrettyPrinter
open Lean.Meta.Tactic.TryThis
open Lean.Meta.Tactic.Cbv Lean.Meta.Sym.Simp

elab "check_validity " S:term:max t:term:max thm:ident : term => do
    let et ← elabTerm t (mkConst ``Nat)
    let eS ← elabTerm S (mkConst ``Scheme)
    let type ← inferType et
    let eSType ← inferType eS
    if eSType.isConstOf ``Scheme then
      let theoremSyntax ← mkAppM thm.getId #[eS, et]
      let rawType ← inferType theoremSyntax
      let rawType ← instantiateMVars rawType
      let result ← cbvEntry rawType
      return Result.getResultExpr rawType result
    else
      throwError "Expected a Scheme and a Nat, but got {eSType} and {type}"


def egScheme : Scheme where
  δ := 1
  hδ := by decide
  t₀ := 0
  x₀ := 1
  m := fun t x => x*x + Rat.pow t 2

example : check_validity egScheme 12 Scheme.x_succ = True := rfl
