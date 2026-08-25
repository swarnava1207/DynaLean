import Mathlib
open Topology
#print IsPicardLindelof
#print Set.Icc
#print ContinuousOn
#check Continuous.continuousOn
#check exists_deriv_eq_slope
#check IsCompact.exists_bound_of_continuousOn'
#check HasDerivWithinAt
#check HasDerivAt.continuousOn
#check HasDerivWithinAt.mono
#check interior_subset
#check Real.toNNReal
#check Continuous.deriv_integral
#check intervalIntegral.integral_same
#check intermediate_value_uIcc
#print NNReal.dist_eq
#print HasDerivWithinAt.mono
#check Set.uIcc_subset_Icc
#check IsCompact.sSup_mem
#print CompleteLinearOrder
#check ContinuousOn.preimage_isClosed_of_isClosed
-- #print le_gronwallBound_of_deriv_right_le

variable {f : ℝ → ℝ → ℝ} {x0 : ℝ} {T : NNReal} {M : NNReal}
def SolutionExistsandConstantBounded := ∃ x : ℝ → ℝ, x 0 = x0
    ∧ (∀ t ∈ Set.Icc (0 :ℝ) T, HasDerivWithinAt x (f (t :ℝ) (x (t :ℝ))) (Set.Icc 0 T) t)
    ∧ (∀ t ∈ Set.Icc (0:ℝ) T, x t ≤ x0 + M * t)
def SolutionExistsandTimeDependentBounded (g : ℝ → ℝ):= ∃ x : ℝ → ℝ, x 0 = x0
    ∧ (∀ t ∈ Set.Icc (0 :ℝ) T, HasDerivWithinAt x (f (t :ℝ) (x (t :ℝ))) (Set.Icc 0 T) t)
    ∧ (∀ t ∈ Set.Icc (0:ℝ) T, x t ≤ x0 + ∫ s in 0..t, g s)



/-
Given `x' = f(t,x)` and `f(t,x) ≤ M`, we want to find bounds on `x(t)` at any time interval in [0,T]
-/
theorem constant_bound_solution (hc : ∀ y, Continuous (fun t => f t y)) (K : NNReal)
      (hl : ∀ t, LipschitzWith K (fun x => f t x))
      (hM : ∀ t x, |f t x| ≤ M) : @SolutionExistsandConstantBounded f x0 T M := by
      let t0 : Set.Icc (0 :ℝ) T := ⟨0, by simp, by simp⟩
      have h1 : IsPicardLindelof f t0 x0 (M*T) 0 M K := by
        apply IsPicardLindelof.mk
        · intro t ht
          simp only [NNReal.coe_mul]
          intro x hx y hy
          simp only [LipschitzWith] at hl
          specialize hl t x y
          assumption
        · intro x hx
          apply Continuous.continuousOn
          apply hc
        · intro t ht x hx
          simp [hM]
        · simp only [sub_zero, NNReal.coe_mul, NNReal.coe_zero]
          cases max_choice ((T : ℝ) - t0) ↑t0 with
          | inl hle =>
            simp only [hle]
            have l0 : t0 ≥ (0 : ℝ) := by
              let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            have l1 : (T : ℝ) - (t0: ℝ) ≤ T := by simp [l0]
            have l2 : (M : ℝ) ≥ 0 := by simp
            have l3 : t0 ≤ (T :ℝ) := by
              let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            apply mul_le_mul <;> simp [l1,l2,l3]
          | inr hge =>
            simp only [hge]
            apply mul_le_mul
            · simp
            · let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            · let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            · simp
      let ⟨x, hx⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ h1
      use x
      constructor
      · exact hx.1
      · constructor
        · exact hx.2
        · intro t ht
          have : t0 = (0 :ℝ) := by grind
          have ht_le : ↑t0 ≤ t := by grind
          have h_bound : ∀ s ∈ Set.Icc (↑t0) t, f s (x s) ≤ ↑M := by
            intro s _
            have h_abs := hM s (x s)
            exact le_trans (le_abs_self (f s (x s))) h_abs
          have h_deriv : ∀ s ∈ Set.Icc (↑t0) t,
                        HasDerivWithinAt x (f s (x s)) (Set.Icc (↑t0) t) s := by
            intro s hs
            have hs_T : s ∈ Set.Icc 0 ↑T := by
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
          simp at h_eval
          linarith


set_option linter.style.longLine false in
/-
Given `x' = f(t,x)` and `f(t,x) ≤ g(t)`, we want to find bounds on `x(t)` at any time interval in [0,T]
-/
theorem time_dependent_bound_solution {g : ℝ → ℝ} (hc : ∀ y, Continuous (fun t => f t y)) (K : NNReal)
      (hgc : Continuous g)
      (hl : ∀ t, LipschitzWith K (fun x => f t x))
      (hg : ∀ t x, |f t x| ≤ g t) : @SolutionExistsandTimeDependentBounded f x0 T g := by
      let t0 : Set.Icc (0 :ℝ) T := ⟨0, by simp, by simp⟩
      have hgb : ∃ M : ℝ, ∀ t ∈ Set.Icc (0:ℝ) T, |g t| ≤ M := by
        have h_cont : ContinuousOn g (Set.Icc (0:ℝ) T) := by
          apply Continuous.continuousOn
          exact hgc
        have h_compact : IsCompact (Set.Icc (0:ℝ) T) := by
          apply isCompact_Icc
        have h_bound := IsCompact.exists_bound_of_continuousOn h_compact h_cont
        cases h_bound with
        | intro M hM =>
          use M
          intro t ht
          specialize hM t ht
          simp only [Real.norm_eq_abs] at hM
          exact hM
      let ⟨M', hM⟩ := hgb
      let M := Real.toNNReal M'
      have real_M : (M : ℝ) = M' := by
        simp [M]
        specialize hM 0 (Set.left_mem_Icc.mpr (by simp))
        grind
      have he : IsPicardLindelof f t0 x0 (M*T) 0 M K := by
        apply IsPicardLindelof.mk
        · intro t ht
          simp only [NNReal.coe_mul]
          intro x hx y hy
          simp only [LipschitzWith] at hl
          specialize hl t x y
          assumption
        · intro x hx
          apply Continuous.continuousOn
          apply hc
        · intro t ht x hx
          simp only [Real.norm_eq_abs]
          specialize hg t x
          specialize hM t ht
          grind
        · simp only [sub_zero, NNReal.coe_mul, NNReal.coe_zero]
          cases max_choice ((T : ℝ) - t0) ↑t0 with
          | inl hle =>
            simp only [hle]
            have l0 : t0 ≥ (0 : ℝ) := by
              let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            have l1 : (T : ℝ) - (t0: ℝ) ≤ T := by simp [l0]
            have l2 : (M : ℝ) ≥ 0 := by simp
            have l3 : t0 ≤ (T :ℝ) := by
              let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            apply mul_le_mul <;> simp [l1,l2,l3]
          | inr hge =>
            simp only [hge]
            apply mul_le_mul
            · simp
            · let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            · let ⟨m, hm⟩ := t0
              simp [Set.mem_Icc.1 hm]
            · simp
      let ⟨x, hx⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ he
      use x
      constructor
      · exact hx.1
      · constructor
        · exact hx.2
        · intro t ht
          have : t0 = (0 :ℝ) := by grind
          have ht_le : ↑t0 ≤ t := by grind
          have h_bound : ∀ s ∈ Set.Icc (↑t0) t, f s (x s) ≤ g s := by
            intro s _
            have h_abs := hg s (x s)
            grind
          have h_deriv : ∀ s ∈ Set.Icc (↑t0) t,
                        HasDerivWithinAt x (f s (x s)) (Set.Icc (↑t0) t) s := by
            intro s hs
            have hs_T : s ∈ Set.Icc 0 ↑T := by
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
          simp at h_eval
          grind [intervalIntegral.integral_same]


theorem comparison_first_order {g : ℝ → ℝ → ℝ} (K : NNReal)
      (hl : ∀ t, LipschitzWith K (fun x => g t x)) (x : ℝ → ℝ) (y : ℝ → ℝ)
      (hb : ∀ t ∈ Set.Icc (0 : ℝ) T, f t (x t) ≤ g t (x t))
      (hxe : x 0 = x0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt x (f (t : ℝ) (x (t : ℝ))) (Set.Icc 0 T) t))
      (hye : y 0 = y0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt y (g (t : ℝ) (y (t : ℝ))) (Set.Icc 0 T) t))
      (hi : x 0 ≤ y 0) : ∀ t ∈ Set.Icc (0 : ℝ) T, x t ≤ y t := by
      intro t ht
      let z := fun s ↦ x s - y s
      have hbz : ∀ s ∈ Set.Icc (0:ℝ) T,
      HasDerivWithinAt z (f s (x s) - g s (y s)) (Set.Icc 0 T) s := by
        intro s hs
        have h1 := (hxe.right s hs).sub (hye.right s hs)
        exact h1
      have hbl : ∀ s ∈ Set.Icc (0:ℝ) T, g s (x s) - g s (y s) ≤ K * |z s| := by
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
      have hbz_le : ∀ s ∈ Set.Icc (0:ℝ) T, f s (x s) - g s (y s) ≤ K * |z s| := by
        intro s hs
        have h1 := hb s hs
        have h2 := hbl s hs
        linarith
      have h0zle : z 0 ≤ 0 := by
        have h1 := hxe.left
        have h2 := hye.left
        grind
      have hzle : ∀ s ∈ Set.Icc (0:ℝ) T, z s ≤ 0 := by
        intro t1 ht1
        by_contra! h_pos
        have : ∃ t0 ∈ Set.Icc (0:ℝ) t1 , z t0 = 0 := by
          have : 0 ∈ z ''(Set.Icc (0:ℝ) t1) := by
            have : 0 ∈ Set.uIcc (z 0) (z t1) := by
              constructor
              · grind [Set.mem_uIcc]
              · grind [Set.mem_uIcc]
            have : Set.uIcc (z 0) (z t1) ⊆ z ''(Set.uIcc (0:ℝ) t1) := by
              apply intermediate_value_uIcc
              apply HasDerivWithinAt.continuousOn
              · intro x1 hx1
                have hx1' : x1 ∈ Set.Icc (0:ℝ) T := by
                  grind [Set.uIcc]
                apply (hbz x1 hx1').mono
                grind [Set.uIcc_subset_Icc]
            have : 0 ∈ z ''(Set.uIcc (0:ℝ) t1) := by grind
            have : Set.uIcc (0:ℝ) t1 = Set.Icc (0:ℝ) t1 := by grind [Set.uIcc]
            grind
          grind
        let S := {t ∈ Set.Icc 0 t1 | z t = 0}
        have hS_nonempty : S.Nonempty := by
          rcases this with ⟨t0, ht0, hz0⟩
          exact ⟨t0, ht0, hz0⟩
        have hS_bdd : BddAbove S := ⟨t1, fun _ h ↦ h.1.2⟩
        let t_last := sSup S
        have ht_last_mem : t_last ∈ S := by
          apply IsClosed.csSup_mem _ hS_nonempty hS_bdd
          have hS_eq : S = Set.Icc 0 t1 ∩ z ⁻¹' {0} := rfl
          rw [hS_eq]
          apply ContinuousOn.preimage_isClosed_of_isClosed
          · intro x1 hx1
            have hx1' : x1 ∈ Set.Icc (0:ℝ) T := by
              grind [Set.uIcc_subset_Icc]
            have hst : Set.Icc 0 t1 ⊆ Set.Icc 0 T := by grind
            have hders : ∀ t ∈ Set.Icc 0 t1,
              HasDerivWithinAt z (f t (x t) - g t (y t)) (Set.Icc 0 t1) t := by
              intro x1 hx1
              have hx1' : x1 ∈ Set.Icc (0:ℝ) T := by
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
              have hx_T : x ∈ Set.Icc 0 (T : ℝ) := by
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
                have hx1' : x1 ∈ Set.Icc (0:ℝ) T := by
                  constructor
                  · grind
                  · exact hx1.2.trans ht1.2
                apply HasDerivWithinAt.mono (hbz x1 hx1')
                grind
            · intro x1 hx1 r hr
              have hx1' : x1 ∈ Set.Icc (0:ℝ) T := by grind
              have h_deriv_x1 := hbz x1 hx1'
              have h_lim : Filter.Tendsto (fun z_1 ↦ (z_1 - x1)⁻¹ • (z z_1 - z x1))
                (𝓝[Set.Icc 0 ↑T \ {x1}] x1) (𝓝 (f x1 (x x1) - g x1 (y x1)))
                  := hasDerivWithinAt_iff_tendsto_slope.mp h_deriv_x1
              have h_ev_smul : ∀ᶠ z_1 in 𝓝[Set.Icc 0 ↑T \ {x1}] x1,
                (z_1 - x1)⁻¹ • (z z_1 - z x1) < r :=
                Filter.Tendsto.eventually h_lim (Iio_mem_nhds hr)
              have h_ev : ∀ᶠ z_1 in 𝓝[Set.Icc 0 ↑T \ {x1}] x1,
                (z_1 - x1)⁻¹ * (z z_1 - z x1) < r := by
                exact h_ev_smul
              have h_mem : Set.Icc 0 ↑T \ {x1} ∈ 𝓝[>] x1 := by
                apply Filter.mem_of_superset (Ioc_mem_nhdsGT hx1.2)
                intro a ha
                exact ⟨⟨hx1'.1.trans_lt ha.1 |>.le, ha.2.trans ht1.2⟩, ha.1.ne'⟩
              have h_le : 𝓝[>] x1 ≤ 𝓝[Set.Icc 0 ↑T \ {x1}] x1 := nhdsWithin_le_of_mem h_mem
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
