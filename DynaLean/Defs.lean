import Mathlib
set_option linter.style.header false
namespace ODE


variable (f : ℝ → ℝ → ℝ) (x₀ : ℝ)
def SolutionExists (x : ℝ → ℝ) (t₀ t₁ : ℝ) (s : Set ℝ) : Prop :=
  x t₀ = x₀ ∧ ∀ t ∈ Set.Icc t₀ t₁, HasDerivWithinAt x (f t (x t)) s t


end ODE
def IsRational (f : ℝ → ℝ → ℝ) : Prop := ∀ t x : ℚ, ∃ p q : ℤ, q ≠ 0 ∧ f t x = p / q
