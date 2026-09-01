import Mathlib
import DynaLean.Defs
open Topology

namespace ODE

theorem comparison_first_order {g : ℝ → ℝ → ℝ} (K : NNReal)
      (hl : ∀ t, LipschitzWith K (fun x => g t x)) (x : ℝ → ℝ) (y : ℝ → ℝ)
      (ht : t₀ ≤ T)
      (hb : ∀ t ∈ Set.Icc t₀ T, f t (x t) ≤ g t (x t))
      (hxe : SolutionExists f x0 x t₀ T (Set.Icc t₀ T))
      (hye : SolutionExists g x0 y t₀ T (Set.Icc t₀ T))
       : ∀ t ∈ Set.Icc t₀ T, x t ≤ y t := by
      intro t ht
      let z := fun s ↦ x s - y s
      have hbz : ∀ s ∈ Set.Icc t₀ T,
      HasDerivWithinAt z (f s (x s) - g s (y s)) (Set.Icc t₀ T) s := by
        intro s hs
        have h1 := (hxe.right s hs).sub (hye.right s hs)
        exact h1
      have hbl : ∀ s ∈ Set.Icc t₀ T, g s (x s) - g s (y s) ≤ K * |z s| := by
        intro s hs
        have h2 := hl s (x s) (y s)
        simp only at h2
        simp only [edist_dist, dist_eq_norm, Real.norm_eq_abs] at h2
        have h3 : |x s - y s| = |z s| := by grind
        rw [h3] at h2
        have h_abs_le : |g s (x s) - g s (y s)| ≤ ↑K * |z s| := by
          have h_rhs : (↑K : ENNReal) * ENNReal.ofReal |z s| = ENNReal.ofReal (↑K * |z s|) := by
            simp only [NNReal.zero_le_coe,
            ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
          rw [h_rhs] at h2
          have h_real := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
          have h_pos : 0 ≤ (↑K : ℝ) * |z s| := mul_nonneg (NNReal.coe_nonneg K) (abs_nonneg _)
          rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal h_pos] at h_real
          exact h_real
        exact le_trans (le_abs_self _) h_abs_le
      have hbz_le : ∀ s ∈ Set.Icc t₀ T, f s (x s) - g s (y s) ≤ K * |z s| := by
        intro s hs
        have h1 := hb s hs
        have h2 := hbl s hs
        linarith
      have h0zle : z t₀ ≤ 0 := by
        have h1 := hxe.left
        have h2 := hye.left
        grind
      have hzle : ∀ s ∈ Set.Icc t₀ T, z s ≤ 0 := by
        intro t1 ht1
        by_contra! h_pos
        have : ∃ t0 ∈ Set.Icc t₀ t1 , z t0 = 0 := by
          have : 0 ∈ z ''(Set.Icc t₀ t1) := by
            have : 0 ∈ Set.uIcc (z t₀) (z t1) := by
              constructor
              · grind [Set.mem_uIcc]
              · grind [Set.mem_uIcc]
            have : Set.uIcc (z t₀) (z t1) ⊆ z ''(Set.uIcc t₀ t1) := by
              apply intermediate_value_uIcc
              apply HasDerivWithinAt.continuousOn
              · intro x1 hx1
                have hx1' : x1 ∈ Set.Icc t₀ T := by
                  grind [Set.uIcc]
                apply (hbz x1 hx1').mono
                grind [Set.uIcc_subset_Icc]
            have : 0 ∈ z ''(Set.uIcc t₀ t1) := by grind
            have : Set.uIcc t₀ t1 = Set.Icc t₀ t1 := by grind [Set.uIcc]
            grind
          grind
        let S := {t ∈ Set.Icc t₀ t1 | z t = 0}
        have hS_nonempty : S.Nonempty := by
          rcases this with ⟨t0, ht0, hz0⟩
          exact ⟨t0, ht0, hz0⟩
        have hS_bdd : BddAbove S := ⟨t1, fun _ h ↦ h.1.2⟩
        let t_last := sSup S
        have ht_last_mem : t_last ∈ S := by
          apply IsClosed.csSup_mem _ hS_nonempty hS_bdd
          have hS_eq : S = Set.Icc t₀ t1 ∩ z ⁻¹' {0} := rfl
          rw [hS_eq]
          apply ContinuousOn.preimage_isClosed_of_isClosed
          · intro x1 hx1
            have hx1' : x1 ∈ Set.Icc t₀ T := by
              grind [Set.uIcc_subset_Icc]
            have hst : Set.Icc t₀ t1 ⊆ Set.Icc t₀ T := by grind
            have hders : ∀ t ∈ Set.Icc t₀ t1,
              HasDerivWithinAt z (f t (x t) - g t (y t)) (Set.Icc t₀ t1) t := by
              intro x1 hx1
              have hx1' : x1 ∈ Set.Icc t₀ T := by
                grind [Set.uIcc_subset_Icc]
              apply (hbz x1 hx1').mono hst
            apply HasDerivWithinAt.continuousOn hders
            exact hx1
          · exact isClosed_Icc
          · exact isClosed_singleton
        have hz_last : z t_last = 0 := by grind
        have hz_pos : ∀ s ∈ Set.Ico t_last t1, 0 ≤ z s := by
            intro s hs
            by_contra! h_neg
            have h_cont : ContinuousOn z (Set.Icc s t1) := by
              intro x hx
              have hx_T : x ∈ Set.Icc t₀ (T : ℝ) := by
                constructor
                · grind
                · exact hx.2.trans ht1.2
              exact (hbz x hx_T).continuousWithinAt.mono (by
                intro y hy
                exact ⟨ht_last_mem.1.1.trans (by grind), hy.2.trans ht1.2⟩)
            have h_ivt : ∃ r ∈ Set.Icc s t1, z r = 0 := by
              apply intermediate_value_Icc (le_of_lt hs.2) h_cont
              grind
            rcases h_ivt with ⟨r, hr_bounds, hr_zero⟩
            have hr_in_S : r ∈ S := by
              constructor
              · constructor
                · grind
                · exact hr_bounds.2
              · exact hr_zero
            have hr_le_sup : r ≤ t_last := le_csSup hS_bdd hr_in_S
            have hr_gt_sup : t_last < r := by grind
            grind
        have hz_deriv : ∀ s ∈ Set.Ico t_last t1, f s (x s) - g s (y s) ≤ K * z s := by
            intro s hs
            have h_abs : |z s| = z s := abs_of_nonneg (hz_pos s hs)
            grind
        have hz_gronwall : ∀ s ∈ Set.Ioc t_last t1, z s ≤ gronwallBound 0 K 0 (s - t_last) := by
            intro s hs
            apply le_gronwallBound_of_liminf_deriv_right_le
            · apply HasDerivWithinAt.continuousOn
              · intro x1 hx1
                have hx1' : x1 ∈ Set.Icc t₀ T := by
                  constructor
                  · grind
                  · exact hx1.2.trans ht1.2
                apply HasDerivWithinAt.mono (hbz x1 hx1')
                grind
            · intro x1 hx1 r hr
              have hx1' : x1 ∈ Set.Icc t₀ T := by grind
              have h_deriv_x1 := hbz x1 hx1'
              have h_lim : Filter.Tendsto (fun z_1 ↦ (z_1 - x1)⁻¹ • (z z_1 - z x1))
                (𝓝[Set.Icc t₀ ↑T \ {x1}] x1) (𝓝 (f x1 (x x1) - g x1 (y x1)))
                  := hasDerivWithinAt_iff_tendsto_slope.mp h_deriv_x1
              have h_ev_smul : ∀ᶠ z_1 in 𝓝[Set.Icc t₀ ↑T \ {x1}] x1,
                (z_1 - x1)⁻¹ • (z z_1 - z x1) < r :=
                Filter.Tendsto.eventually h_lim (Iio_mem_nhds hr)
              have h_ev : ∀ᶠ z_1 in 𝓝[Set.Icc t₀ ↑T \ {x1}] x1,
                (z_1 - x1)⁻¹ * (z z_1 - z x1) < r := by
                exact h_ev_smul
              have h_mem : Set.Icc t₀ ↑T \ {x1} ∈ 𝓝[>] x1 := by
                apply Filter.mem_of_superset (Ioc_mem_nhdsGT hx1.2)
                intro a ha
                exact ⟨⟨hx1'.1.trans_lt ha.1 |>.le, ha.2.trans ht1.2⟩, ha.1.ne'⟩
              have h_le : 𝓝[>] x1 ≤ 𝓝[Set.Icc t₀ ↑T \ {x1}] x1 := nhdsWithin_le_of_mem h_mem
              have h_ev_right : Filter.Eventually
                  (fun z_1 ↦ (z_1 - x1)⁻¹ * (z z_1 - z x1) < r) (𝓝[>] x1) :=
                    h_le h_ev
              exact Filter.Eventually.frequently h_ev_right
            · grind
            · intro s hs
              specialize hz_deriv s hs
              grind
            · grind
        have hzt1 : z t1 ≤ 0 := by
          specialize hz_gronwall t1 (by grind)
          simp [gronwallBound] at hz_gronwall
          assumption
        grind
      grind

end ODE
