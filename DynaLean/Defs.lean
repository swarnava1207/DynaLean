module

public import Mathlib
set_option linter.style.header false


@[expose] public section

/-! # Core definitions

The vocabulary shared by every other module in DynaLean:

* `ODE.SolutionExists` and `ODE.SolutionExistsVector` — what it means for a function to
  solve the initial value problem `x' = f t x`, `x t₀ = x₀`, in the scalar and the
  finite-dimensional case respectively;
* the notations `ℝ^n` and `ℚ^n` for `EuclideanSpace ℝ (Fin n)` and
  `EuclideanSpace ℚ (Fin n)`, together with the coercion `ℚ^n → ℝ^n`;
* `ODE.clamp` — nearest-point projection of a real number into an interval;
* `ODE.extend` — the constant extension of a vector field that is only meaningful on a
  compact box, used to turn local hypotheses into global ones.
-/

namespace ODE
section OneDDef
variable (f : ℝ → ℝ → ℝ) (x₀ : ℝ)

/-- A predicate expressing that `x` solves the ODE driven by `f` on an interval.

`SolutionExists f x₀ x t₀ t₁ s` says that `x t₀ = x₀` and that at every time of
`Icc t₀ t₁` the function `x` has derivative `f t (x t)` *within the set `s`*. Taking
`s = Set.Icc t₀ t₁` (as every downstream result does) gives the usual notion of a
solution on a closed interval, with one-sided derivatives at the endpoints. -/
def SolutionExists (x : ℝ → ℝ) (t₀ t₁ : ℝ) (s : Set ℝ) : Prop :=
  x t₀ = x₀ ∧ ∀ t ∈ Set.Icc t₀ t₁, HasDerivWithinAt x (f t (x t)) s t
end OneDDef

section nDDef
open Lean Meta Elab Term

/-! ## Notation for finite-dimensional state spaces

`ℝ^n` and `ℚ^n` elaborate to `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℚ (Fin n)`,
i.e. `Fin n → ℝ` (resp. `Fin n → ℚ`) carried with the `L²` norm. The `atomic` prefix
makes the parser commit to the notation as soon as it sees `ℝ^`, so that `ℝ^n` is never
mistaken for a power of a real number. -/

/-- `ℝ^n` denotes `EuclideanSpace ℝ (Fin n)`: the `L²`-normed space of `n` reals. -/
syntax atomic("ℝ^"term) : term
/-- `ℚ^n` denotes `EuclideanSpace ℚ (Fin n)`: the exactly representable state vectors
used by the numerical schemes. -/
syntax atomic("ℚ^"term) : term

-- Elaborator for the `ℝ^n` and `ℚ^n` notations declared just above: elaborate the
-- exponent as a `ℕ`, build `Fin n`, and wrap it in `EuclideanSpace`.
elab_rules : term
  | `(term| ℝ^$n) => do
  let n ← elabTerm n none
  let t ← mkAppM ``Fin #[n]
  Term.synthesizeSyntheticMVarsNoPostponing
  let t ← mkAppM ``EuclideanSpace #[mkConst ``Real , t]
  return t
  | `(term| ℚ^$n) => do
  let n ← elabTerm n none
  let t ← mkAppM ``Fin #[n]
  Term.synthesizeSyntheticMVarsNoPostponing
  let t ← mkAppM ``EuclideanSpace #[mkConst ``Rat , t]
  return t



/-- Coerce a rational state vector to a real one, coordinatewise.

This is what lets a numerical scheme (which lives in `ℚ^n`, so that its iterates are
exact and computable) be compared with an analytic solution (which lives in `ℝ^n`). -/
instance {n : ℕ} : Coe (ℚ^n) (ℝ^n) where
  coe := fun x => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => (x i : ℝ))

/-- The vector-valued analogue of `ODE.SolutionExists`.

`SolutionExistsVector f x₀ x t₀ t₁ s` says that `x t₀ = x₀` and that at every time of
`Icc t₀ t₁` the curve `x : ℝ → ℝ^n` has derivative `f t (x t)` within `s`. The
derivative is the `HasDerivWithinAt` of a curve, so it is a vector in `ℝ^n`. -/
def SolutionExistsVector {n : ℕ} (f : ℝ → (ℝ^n) → ℝ^n) (x₀ : ℝ^n)
 (x : ℝ → ℝ^n) (t₀ t₁ : ℝ) (s : Set ℝ) : Prop :=
  x t₀ = x₀ ∧ ∀ t ∈ Set.Icc t₀ t₁, HasDerivWithinAt x (f t (x t)) s t


end nDDef

/-! ## Clamping a real number into an interval -/

/-- Clamp `y` into `[a, b]`: the nearest-point projection when `a ≤ b`. -/
noncomputable def clamp (a b y : ℝ) : ℝ := max a (min b y)

/-- The clamped value lies in the target interval. -/
theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (y : ℝ) : clamp a b y ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- Clamping leaves values already in the interval unchanged. -/
theorem clamp_eq_self {a b y : ℝ} (hy : y ∈ Set.Icc a b) : clamp a b y = y := by
  rw [clamp, min_eq_right hy.2, max_eq_right hy.1]

/-- Clamping is nonexpansive, hence Lipschitz with constant `1`. -/
theorem lipschitzWith_clamp (a b : ℝ) : LipschitzWith 1 (clamp a b) :=
  (LipschitzWith.id.const_min b).const_max a

/-! ## The constant extension of a locally defined vector field -/

/-- Extend `f`, a priori only meaningful on `Icc t₀ T ×ˢ closedBall c r`, to all of `ℝ × ℝ`
by clamping both arguments into that box.  The extension is constant in each direction
outside the box, and agrees with `f` on it. -/
noncomputable def extend (f : ℝ → ℝ → ℝ) (t₀ T c r : ℝ) : ℝ → ℝ → ℝ :=
  fun t y => f (clamp t₀ T t) (clamp (c - r) (c + r) y)

end ODE
