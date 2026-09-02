import Mathlib
set_option linter.style.header false
namespace ODE


variable (f : ℝ → ℝ → ℝ) (x₀ : ℝ)

/-- A predicate expressing that `x` solves the ODE driven by `f` on an interval. -/
def SolutionExists (x : ℝ → ℝ) (t₀ t₁ : ℝ) (s : Set ℝ) : Prop :=
  x t₀ = x₀ ∧ ∀ t ∈ Set.Icc t₀ t₁, HasDerivWithinAt x (f t (x t)) s t

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
