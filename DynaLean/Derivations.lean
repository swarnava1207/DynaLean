import Mathlib
import DynaLean.Defs


namespace ODE
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

end ODE
