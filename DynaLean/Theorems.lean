import Mathlib

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
#search "edist for real is just abs?"
#print NNReal.dist_eq


variable (f : ℝ → ℝ → ℝ) (x0 : ℝ) (T : NNReal) (M : NNReal)
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
      (hM : ∀ t x, |f t x| ≤ M) : SolutionExistsandConstantBounded f x0 T M := by
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
      (hg : ∀ t x, |f t x| ≤ g t) : SolutionExistsandTimeDependentBounded f x0 T g := by
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
      (hfc : ∀ y, Continuous (fun t => f t y)) (hgc : ∀ y, Continuous (fun t => g t y))
      (hl : ∀ t, LipschitzWith K (fun x => g t x)) (x : ℝ → ℝ) (y : ℝ → ℝ)
      (hb : ∀ t ∈ Set.Icc (0:ℝ) T, f t (x t) ≤ g t (x t))
      (hxe : x 0 = x0 ∧ (∀ t ∈ Set.Icc (0 :ℝ) T, HasDerivWithinAt x (f (t : ℝ) (x (t : ℝ))) (Set.Icc 0 T) t))
      (hye : y 0 = x0 ∧ (∀ t ∈ Set.Icc (0 :ℝ) T, HasDerivWithinAt y (g (t : ℝ) (y (t : ℝ))) (Set.Icc 0 T) t))
      (hi : x 0 ≤ y 0) : ∀ t ∈ Set.Icc (0:ℝ) T, x t ≤ y t := by
      intro t ht
      let z := fun s ↦ x s - y s
      have hbz : ∀ s ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt z (f s (x s) - g s (y s)) (Set.Icc 0 T) s := by
        intro s hs
        have h1 := (hxe.right s hs).sub (hye.right s hs)
        exact h1
      have hbl : ∀ s ∈ Set.Icc (0:ℝ) T, g s (x s) - g s (y s) ≤ K * |z s| := by
        intro s hs
        have h2 := hl s (x s) (y s)
        simp at h2
        simp [edist_dist, dist_eq_norm] at h2
        have h3 : |x s - y s| = |z s| := by grind
        rw [h3] at h2
        have h_abs_le : |g s (x s) - g s (y s)| ≤ ↑K * |z s| := by
          have h_rhs : (↑K : ENNReal) * ENNReal.ofReal |z s| = ENNReal.ofReal (↑K * |z s|) := by simp
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
      
