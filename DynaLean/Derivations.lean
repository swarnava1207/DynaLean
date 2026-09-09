import Mathlib
import DynaLean.Defs

namespace ODE
variable {f : ℝ → ℝ → ℝ} {t₀ x₀ : ℝ}

theorem solution_regularOn (hf : ContDiff ℝ 1 (fun t : ℝ × ℝ => f t.1 t.2))
    (y : ℝ → ℝ) (hy : SolutionExists f (y a) y a b (Set.Icc a b))
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
      have hpair : ContinuousOn (fun t : ℝ => (t, y t)) (Set.Icc a b) :=
        continuousOn_id.prodMk hdiff.continuousOn
      exact hf.continuous.comp_continuousOn hpair
    have hy1 : ContDiffOn ℝ 1 y (Set.Icc a b) :=
      (contDiffOn_one_iff_derivWithin hu).2 ⟨hdiff, hFc.congr hkey⟩
    have hF1 : ContDiffOn ℝ 1 (fun t : ℝ => f t (y t)) (Set.Icc a b) := by
      have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, y t)) (Set.Icc a b) :=
        contDiffOn_id.prodMk hy1
      exact hf.comp_contDiffOn hpair
    exact hF1.congr hkey



end ODE
#check UniqueDiffWithinAt
