module

public import Mathlib
public import DynaLean.Defs

/-! # Regularity of solutions, and bounds on the second derivative

The Euler error bounds in `DynaLean.EulerBound` take two hypotheses about the exact
solution `y` as given: that it is `C²` on `[a, b]`, and that `‖y''‖ ≤ M` there. This
module discharges both from a hypothesis about the *vector field* instead, which is
what a user actually has in hand.

The bootstrap is the usual one: `y' = f t (y t)` is continuous because `f` and `y` are,
so `y` is `C¹`; but then `t ↦ f t (y t)` is itself `C¹`, so `y` is `C²`
(`ODE.solution_regularOn`). Compactness of `[a, b]` then bounds the continuous second
derivative (`ODE.bounded_iterated_deriv_two`).

Section `Scalar` treats `ℝ`-valued solutions and section `Vector` the `ℝ^k`-valued
ones; the two developments are identical up to `|·|` versus `‖·‖`.

Note that this module is a plain (non-`module`) Lean file and is not re-exported by the
root `DynaLean` module; import `DynaLean.Derivations` directly to use it.
-/
@[expose] public section

namespace ODE


section Scalar

/-! ## Scalar solutions -/

variable {f : ℝ → ℝ → ℝ} {t₀ x₀ : ℝ}
set_option linter.style.longLine false in
/-- `y` is C^2 on the open interval `(a, b)` if it is the solution of `f` and `f` is C^1 on the closed interval `[a, b] × ℝ`. -/
theorem solution_regularOn
    (hf : ContDiffOn ℝ 1 (fun t : ℝ × ℝ => f t.1 t.2) ((Set.Icc a b) ×ˢ Set.univ))
    (y : ℝ → ℝ) (hy : SolutionExists f x₀ y a b (Set.Icc a b))
    : a < b → (ContDiffOn ℝ 2 y <| Set.Icc a b) := by
  intro hab
  change ContDiffOn ℝ (1 + 1) y (Set.Icc a b)
  rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
  apply And.intro
  · intro t ht
    apply HasDerivWithinAt.differentiableWithinAt ((hy.2 t ht).mono (by grind))
  · apply And.intro (by intro h; contradiction)
    have hu : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
    have hd : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (f t (y t)) (Set.Icc a b) t := hy.2
    have hkey : ∀ t ∈ Set.Icc a b, derivWithin y (Set.Icc a b) t = f t (y t) :=
      fun t ht => (hd t ht).derivWithin (hu t ht)
    have hdiff : DifferentiableOn ℝ y (Set.Icc a b) :=
      fun t ht => (hd t ht).differentiableWithinAt
    have hFc : ContinuousOn (fun t : ℝ => f t (y t)) (Set.Icc a b) := by
      intro t ht
      have hpair : ContinuousOn (fun t : ℝ => (t, y t)) (Set.Icc a b) :=
        continuousOn_id.prodMk hdiff.continuousOn
      have := (hf.continuousOn (t, y t) (by grind))
      let p := fun z => (z, y z)
      have triv : ∀ z, (fun t => f t (y t)) z = (f (p z).1 (p z).2) := by grind
      let fu : ℝ × ℝ → ℝ := fun z => f z.1 z.2
      have hkey2 : ∀ z, fu (p z) = f (p z).1 (p z).2 := by grind
      apply ContinuousOn.congr _ (by intro z hz;rw [triv, ← hkey2])
      · exact ht
      · apply hf.continuousOn.comp hpair
        intro s hs
        simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
        grind
    have hy1 : ContDiffOn ℝ 1 y (Set.Icc a b) :=
      (contDiffOn_one_iff_derivWithin hu).2 ⟨hdiff, hFc.congr hkey⟩
    have hF1 : ContDiffOn ℝ 1 (fun t : ℝ => f t (y t)) (Set.Icc a b) := by
      have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, y t)) (Set.Icc a b) :=
        contDiffOn_id.prodMk hy1
      let p := fun z => (z, y z)
      let fu : ℝ × ℝ → ℝ := fun z => f z.1 z.2
      have hkey2 : ∀ z, fu (p z) = f (p z).1 (p z).2 := by grind
      have triv : ∀ z, f z (y z) = (f (p z).1 (p z).2) := by grind
      apply ContDiffOn.congr _ (by intro z hz;rw [triv, ← hkey2])
      apply hf.comp hpair
      intro s hs
      simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
      grind
    exact hF1.congr hkey

set_option linter.style.longLine false in
/-- `y''` is bounded on the open interval `(a, b)` if it is the solution of `f` and `f` is C^1 on the closed interval `[a, b] × ℝ`. -/
theorem bounded_iterated_deriv_two
    (hf : ContDiffOn ℝ 1 (fun t : ℝ × ℝ => f t.1 t.2) ((Set.Icc a b) ×ˢ Set.univ))
    (y : ℝ → ℝ) (hy : SolutionExists f x₀ y a b (Set.Icc a b))
    : a < b → ∃ M, ∀ t ∈ Set.Ioo a b, |iteratedDeriv 2 y t| ≤ M := by
  intro hab
  have hy2 := solution_regularOn hf y hy hab
  have hcont : ContinuousOn (iteratedDerivWithin 2 y (Set.Icc a b)) (Set.Icc a b) :=
        hy2.continuousOn_iteratedDerivWithin (m := 2) (by grind) (uniqueDiffOn_Icc hab)
  have hkey : ∀ t ∈ Set.Ioo a b, iteratedDeriv 2 y t = iteratedDerivWithin 2 y (Set.Icc a b) t := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (by exact hy2.contDiffAt (by simp only [Icc_mem_nhds_iff, Set.mem_Ioo]; grind))]
    grind
  have hb : ∃ M, ∀ t ∈ Set.Ioo a b, |iteratedDerivWithin 2 y (Set.Icc a b) t| ≤ M := by
    let ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    use M
    intro t ht
    specialize hM t (by grind)
    simp only [Real.norm_eq_abs] at hM
    exact hM
  let ⟨M, hM⟩ := hb
  use M
  intro t ht
  specialize hM t (by grind)
  rw [← hkey t ht] at hM
  exact hM

end Scalar


section Vector

/-! ## Vector-valued solutions

The same two results for `ℝ^k`-valued solutions, with the absolute value replaced by
the Euclidean norm. The proofs are the scalar ones transcribed verbatim. -/

variable {k : ℕ} {f : ℝ → (ℝ^k) → ℝ^k} {t₀ x₀ : ℝ^k}

set_option linter.style.longLine false in
/-- `y` is C^2 on `[a, b]` if it is an `ℝ^k`-valued solution of `f` and `f` is C^1 on `[a, b] × ℝ^k`.

The `ℝ^k` analogue of `ODE.solution_regularOn`. -/
theorem solution_regularOn_vector
    (hf : ContDiffOn ℝ 1 (fun t : ℝ × ℝ^k => f t.1 t.2) ((Set.Icc a b) ×ˢ Set.univ))
    (y : ℝ → ℝ^k) (hy : SolutionExistsVector f x₀ y a b (Set.Icc a b))
    : a < b → (ContDiffOn ℝ 2 y <| Set.Icc a b) := by
  intro hab
  change ContDiffOn ℝ (1 + 1) y (Set.Icc a b)
  rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
  apply And.intro
  · intro t ht
    apply HasDerivWithinAt.differentiableWithinAt ((hy.2 t ht).mono (by grind))
  · apply And.intro (by intro h; contradiction)
    have hu : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
    have hd : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (f t (y t)) (Set.Icc a b) t := hy.2
    have hkey : ∀ t ∈ Set.Icc a b, derivWithin y (Set.Icc a b) t = f t (y t) :=
      fun t ht => (hd t ht).derivWithin (hu t ht)
    have hdiff : DifferentiableOn ℝ y (Set.Icc a b) :=
      fun t ht => (hd t ht).differentiableWithinAt
    have hFc : ContinuousOn (fun t : ℝ => f t (y t)) (Set.Icc a b) := by
      intro t ht
      have hpair : ContinuousOn (fun t : ℝ => (t, y t)) (Set.Icc a b) :=
        continuousOn_id.prodMk hdiff.continuousOn
      have := (hf.continuousOn (t, y t) (by grind))
      let p := fun z => (z, y z)
      have triv : ∀ z, (fun t => f t (y t)) z = (f (p z).1 (p z).2) := by grind
      let fu : ℝ × (ℝ^k) → ℝ^k := fun z => f z.1 z.2
      have hkey2 : ∀ z, fu (p z) = f (p z).1 (p z).2 := by grind
      apply ContinuousOn.congr _ (by intro z hz;rw [triv, ← hkey2])
      · exact ht
      · apply hf.continuousOn.comp hpair
        intro s hs
        simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
        grind
    have hy1 : ContDiffOn ℝ 1 y (Set.Icc a b) :=
      (contDiffOn_one_iff_derivWithin hu).2 ⟨hdiff, hFc.congr hkey⟩
    have hF1 : ContDiffOn ℝ 1 (fun t : ℝ => f t (y t)) (Set.Icc a b) := by
      have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, y t)) (Set.Icc a b) :=
        contDiffOn_id.prodMk hy1
      let p := fun z => (z, y z)
      let fu : ℝ × (ℝ^k) → ℝ^k := fun z => f z.1 z.2
      have hkey2 : ∀ z, fu (p z) = f (p z).1 (p z).2 := by grind
      have triv : ∀ z, f z (y z) = (f (p z).1 (p z).2) := by grind
      apply ContDiffOn.congr _ (by intro z hz;rw [triv, ← hkey2])
      apply hf.comp hpair
      intro s hs
      simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
      grind
    exact hF1.congr hkey


set_option linter.style.longLine false in
/-- `‖y''‖` is bounded on `(a, b)` if `y` is an `ℝ^k`-valued solution of `f` and `f` is C^1 on `[a, b] × ℝ^k`.

The `ℝ^k` analogue of `ODE.bounded_iterated_deriv_two`; this supplies the constant `M`
required by the vector Euler bounds in `DynaLean.EulerBound`. -/
theorem bounded_iterated_deriv_two_vector
    (hf : ContDiffOn ℝ 1 (fun t : ℝ × ℝ^k => f t.1 t.2) ((Set.Icc a b) ×ˢ Set.univ))
    (y : ℝ → ℝ^k) (hy : SolutionExistsVector f x₀ y a b (Set.Icc a b))
    : a < b → ∃ M, ∀ t ∈ Set.Ioo a b, ‖iteratedDeriv 2 y t‖ ≤ M := by
  intro hab
  have hy2 := solution_regularOn_vector hf y hy hab
  have hcont : ContinuousOn (iteratedDerivWithin 2 y (Set.Icc a b)) (Set.Icc a b) :=
        hy2.continuousOn_iteratedDerivWithin (m := 2) (by grind) (uniqueDiffOn_Icc hab)
  have hkey : ∀ t ∈ Set.Ioo a b, iteratedDeriv 2 y t = iteratedDerivWithin 2 y (Set.Icc a b) t := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (by exact hy2.contDiffAt (by simp only [Icc_mem_nhds_iff, Set.mem_Ioo]; grind))]
    grind
  have hb : ∃ M, ∀ t ∈ Set.Ioo a b, ‖iteratedDerivWithin 2 y (Set.Icc a b) t‖ ≤ M := by
    let ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    use M
    intro t ht
    specialize hM t (by grind)
    exact hM
  let ⟨M, hM⟩ := hb
  use M
  intro t ht
  specialize hM t (by grind)
  rw [← hkey t ht] at hM
  exact hM
end Vector
end ODE
