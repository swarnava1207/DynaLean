import Mathlib
import DynaLean.Defs
open Topology


variable {f : ℝ → ℝ → ℝ} {x0 : ℝ} {t₀ T : ℝ} {M : NNReal}

namespace ODE
/-- Bound a solution using a uniform absolute bound on the vector field. -/
theorem constant_bound_solution (x : ℝ → ℝ) (ht : t₀ ≤ T)
      (hx : SolutionExists f x0 x t₀ T (Set.Icc t₀ T))
      (hM : ∀ t x, |f t x| ≤ M) : ∀ t ∈ Set.Icc t₀ T, x t ≤ x0 + M * (t - t₀) := by
      let t0 : Set.Icc t₀ T := ⟨t₀, by simp, ht⟩
      intro t ht
      have ht_le : ↑t0 ≤ t := by grind
      have h_bound : ∀ s ∈ Set.Icc (↑t0) t, f s (x s) ≤ ↑M := by
        intro s _
        have h_abs := hM s (x s)
        exact le_trans (le_abs_self (f s (x s))) h_abs
      have h_deriv : ∀ s ∈ Set.Icc (↑t0) t,
                    HasDerivWithinAt x (f s (x s)) (Set.Icc (↑t0) t) s := by
        intro s hs
        have hs_T : s ∈ Set.Icc ↑t0 ↑T := by
          constructor
          · exact le_trans t0.property.1 hs.1
          · exact le_trans hs.2 ht.2
        exact (hx.right s hs_T).mono (by
          intro y hy
          exact ⟨le_trans t0.property.1 hy.1, le_trans hy.2 ht.2⟩)
      have h_anti : AntitoneOn (fun s ↦ x s - ↑M * s) (Set.Icc (↑t0) t) := by
        refine @antitoneOn_of_hasDerivWithinAt_nonpos (Set.Icc t0 t) (convex_Icc (↑t0) t)
          (fun s ↦ x s - (M : ℝ) * s) (fun s ↦ f s (x s) - (M :ℝ)) ?_ ?_ ?_
        · apply HasDerivWithinAt.continuousOn
          · intro x1 hx1
            apply HasDerivWithinAt.sub
            · exact (h_deriv x1 hx1)
            · have h2 : HasDerivAt (fun r ↦ (M : ℝ) * r) ↑M x1 := by
                have h_id : HasDerivAt (fun r ↦ r) 1 x1 := hasDerivAt_id x1
                have h_mul := HasDerivAt.const_mul ↑M h_id
                simpa only [mul_one] using h_mul
              exact h2.hasDerivWithinAt
        · intro s hs
          have h1 := (h_deriv s (by grind [interior_subset])).mono
                      (by grind [interior_subset]: interior (Set.Icc (↑t0) t) ⊆ Set.Icc (↑t0) t)
          have h2 : HasDerivAt (fun r ↦ (M : ℝ) * r) ↑M s := by
            have h_id : HasDerivAt (fun r ↦ r) 1 s := hasDerivAt_id s
            have h_mul := HasDerivAt.const_mul ↑M h_id
            simpa only [mul_one] using h_mul
          exact h1.sub h2.hasDerivWithinAt
        · intro s hs
          -- Prove that x'(s) - M ≤ 0 using your h_bound
          linarith [h_bound s (by grind [interior_subset])]
      have h_eval := h_anti (Set.left_mem_Icc.mpr ht_le) (Set.right_mem_Icc.mpr ht_le) ht_le
      simp only [tsub_le_iff_right] at h_eval
      rw [hx.1] at h_eval
      grind


set_option linter.style.longLine false in
/-- Bound a solution using a continuous time-dependent upper bound on the vector field. -/
theorem time_dependent_bound_solution {g : ℝ → ℝ} (x : ℝ → ℝ) (hgc : Continuous g)
      (hx : SolutionExists f x0 x t₀ T (Set.Icc t₀ T)) (ht : t₀ ≤ T)
      (hg : ∀ t x, |f t x| ≤ g t) : ∀ t ∈ Set.Icc t₀ T, x t ≤ x0 + ∫ s in t₀..t, g s:= by
      let t0 : Set.Icc t₀ T := ⟨t₀, by simp, ht⟩
      intro t ht
      have ht_le : ↑t0 ≤ t := by grind
      have h_bound : ∀ s ∈ Set.Icc (↑t0) t, f s (x s) ≤ g s := by
        intro s _
        have h_abs := hg s (x s)
        grind
      have h_deriv : ∀ s ∈ Set.Icc (↑t0) t,
                    HasDerivWithinAt x (f s (x s)) (Set.Icc (↑t0) t) s := by
        intro s hs
        have hs_T : s ∈ Set.Icc ↑t0 ↑T := by
          constructor
          · exact le_trans t0.property.1 hs.1
          · exact le_trans hs.2 ht.2
        exact (hx.right s hs_T).mono (by
          intro y hy
          exact ⟨le_trans t0.property.1 hy.1, le_trans hy.2 ht.2⟩)
      have h_anti : AntitoneOn (fun s ↦ x s - ∫ r in 0..s, g r) (Set.Icc (↑t0) t) := by
        refine @antitoneOn_of_hasDerivWithinAt_nonpos (Set.Icc t0 t) (convex_Icc (↑t0) t)
          (fun s ↦ x s - ∫ r in 0..s, g r) (fun s ↦ f s (x s) - g s) ?_ ?_ ?_
        · apply HasDerivWithinAt.continuousOn
          · intro x1 hx1
            apply HasDerivWithinAt.sub
            · exact (h_deriv x1 hx1)
            · have h2 : HasDerivAt (fun r ↦ ∫ s in 0..r, g s) (g x1) x1 := by
                exact (hgc.integral_hasStrictDerivAt 0 x1).hasDerivAt
              exact h2.hasDerivWithinAt
        · intro s hs
          have h1 := (h_deriv s (by grind [interior_subset])).mono
                      (by grind [interior_subset]: interior (Set.Icc (↑t0) t) ⊆ Set.Icc (↑t0) t)
          have h2 : HasDerivAt (fun r ↦ ∫ s in 0..r, g s) (g s) s := by
                    exact (hgc.integral_hasStrictDerivAt 0 s).hasDerivAt
          exact h1.sub h2.hasDerivWithinAt
        · intro s hs
          -- Prove that x'(s) - g(s) ≤ 0 using your h_bound
          linarith [h_bound s (by grind [interior_subset])]
      have h_eval := h_anti (Set.left_mem_Icc.mpr ht_le) (Set.right_mem_Icc.mpr ht_le) ht_le
      simp only [tsub_le_iff_right] at h_eval
      rw [hx.1] at h_eval
      calc
        _ ≤ (x0 - ∫ r in 0..↑t0, g r) + ∫ r in 0..t, g r := by grind
        _ = x0 + (∫ r in 0..t, g r) - ∫ r in 0..↑t0, g r := by ring
        _ = x0 + ((∫ r in 0..t, g r) - (∫ r in 0..↑t0, g r)) := by ring
        _ = x0 + ∫ r in ↑t0..t, g r := by
          rw [intervalIntegral.integral_interval_sub_left] <;> apply hgc.continuousOn.intervalIntegrable


end ODE
