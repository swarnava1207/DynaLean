import Mathlib
open Topology
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
#check intervalIntegral.integral_comp_mul_deriv'
variable {f : ℝ → ℝ → ℝ}
theorem nonneg_integral_bound (g : ℝ → ℝ) (hfc : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (hgc : Continuous g) (w : ℝ → ℝ) (hwc : Continuous w) (x : ℝ → ℝ)
      (hgb : ∀ t ∈ Set.Icc (0 : ℝ) T, g t ≥ 0) (hwmono : MonotoneOn w (Set.Ioi (0 : ℝ))) (u₀ : ℝ)
      (hu₀ : u₀ ∈ Set.Ioi (0 : ℝ))
      (hx : x 0 = x0 ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt x (f t (x t)) (Set.Icc 0 T) t))
      (hfb : (∀ t ∈ Set.Icc (0 : ℝ) T, f t (x t) ≤ g t * w (x t)))
      (hwb : ∀ u ∈ Set.Ici (0 : ℝ), w u > 0)
      (hxb : ∀ t ∈ Set.Icc (0 : ℝ) T, x t ≥ 0) :
      ∃ G : ℝ → ℝ, (∀ u ∈ Set.Ioi (0 : ℝ),  G u = ∫ t in u₀..u, 1 / w t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, x t ≤ G⁻¹ (G x0 + ∫ s in 0..t, g s)) := by
      let G : ℝ → ℝ := fun u => ∫ t in u₀..u, 1 / w t
      have hG : ∀ u ∈ Set.Ioi (0 : ℝ), G u = ∫ t in u₀..u, 1 / w t := by
        intro u hu
        simp [G]
      use G
      constructor
      · exact hG
      · intro t ht
        -- have hG' : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt G (1 / w u) u := by
        --   intro u hu
        --   have hw_pos : w u > 0 := hwb u hu
        --   have hw_cont : ContinuousAt w u := hwc.continuousAt
        --   have hw_ne_zero : w u ≠ 0 := by linarith
        --   have h_inv_cont : ContinuousAt (fun x => (w x)⁻¹) u := by
        --     apply ContinuousAt.inv₀ <;> assumption
        --   have hG_deriv : HasDerivAt (fun x => ∫ t in u₀..x, 1 / w t) (1 / w u) u := by
        --     apply intervalIntegral.integral_hasDerivAt_right
        --     · rw [intervalIntegrable_iff]
        --       sorry
        --     · sorry
        --     · grind
        have hx_div : ∀ t ∈ Set.Ioc (0 : ℝ) T, f t (x t) / w (x t) ≤ g t := by
          intro t ht
          specialize hfb t (by grind)
          specialize hxb t (by grind)
          specialize hwb (x t) (by grind)
          rw [div_le_iff₀' hwb]
          grind
        have hx_int : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ s in 0..t, f s (x s) / w (x s) ≤ ∫ s in 0..t, g s := by
          intro t ht
          apply intervalIntegral.integral_mono_on_of_le_Ioo ht.1
          · have hx_cont : ContinuousOn x (Set.Icc 0 t) := by
              intro u hu
              have h_in_T : u ∈ Set.Icc 0 T := ⟨hu.1, le_trans hu.2 ht.2⟩
              exact (hx.2 u h_in_T).continuousWithinAt.mono (Set.Icc_subset_Icc le_rfl ht.2)
            apply ContinuousOn.intervalIntegrable_of_Icc ht.1
            apply ContinuousOn.div
            · have h_pair : ContinuousOn (fun u ↦ (u, x u)) (Set.Icc 0 t) :=
                ContinuousOn.prodMk continuousOn_id hx_cont
              exact hfc.comp_continuousOn h_pair
            · exact hwc.comp_continuousOn hx_cont
            · intro u hu
              have h_in_T : u ∈ Set.Icc 0 T := ⟨hu.1, le_trans hu.2 ht.2⟩
              have hxu_nonneg : x u ≥ 0 := hxb u h_in_T
              have hwu_pos : w (x u) > 0 := hwb (x u) hxu_nonneg
              exact ne_of_gt hwu_pos
          · exact Continuous.intervalIntegrable hgc 0 t
          · intro s hs
            specialize hx_div s (by grind)
            grind
        have hx_subst : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ u in (x 0)..(x t), 1 / w u ≤ ∫ s in 0..t, g s := by
          intro t ht
          let k := fun x => 1 / w x
          have : ∫ u in (x 0)..(x t), 1 / w u = ∫ u in (x 0)..(x t), k u := by grind
          rw [this]
          rw [← intervalIntegral.integral_comp_mul_deriv']
          · specialize hx_int t ht
            have : ∀ s ∈ Set.Icc (0 : ℝ) T, f s (x s) / w (x s) = 1 / w (x s) * f s (x s) :=
              by intro s hs; rw [div_eq_mul_one_div]; grind
            have hint_eq : ∫ (s : ℝ) in 0..t, f s (x s) / w (x s) = ∫ (s : ℝ) in 0..t, (k ∘ x) s * f s (x s) := by
              apply intervalIntegral.integral_congr
              intro s hs
              rw [Set.uIcc_of_le ht.1] at hs
              have hs_T : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
              exact this s hs_T
            rw [hint_eq] at hx_int
            exact hx_int
          · intro m hm
            have m_in_T : m ∈ Set.Icc 0 T := by
              rw [Set.uIcc_of_le ht.1] at hm
              grind
            have open_sub_closed : Set.Ioo (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) T := by
              intro u hu
              grind
            apply (HasDerivWithinAt.mono (hx.2 m m_in_T) open_sub_closed).hasDerivAt
            rw [Set.uIcc_of_le ht.1] at hm
            rw [IsOpen.mem_nhds_iff]
            · sorry
            · sorry
          · have hx_cont : ContinuousOn x (Set.Icc 0 t) := by
              intro u hu
              have h_in_T : u ∈ Set.Icc 0 T := ⟨hu.1, le_trans hu.2 ht.2⟩
              exact (hx.2 u h_in_T).continuousWithinAt.mono (Set.Icc_subset_Icc le_rfl ht.2)
            have h_pair : ContinuousOn (fun u ↦ (u, x u)) (Set.Icc 0 t) :=
                ContinuousOn.prodMk continuousOn_id hx_cont
            rw [Set.uIcc_of_le ht.1]
            exact hfc.comp_continuousOn h_pair
          · apply ContinuousOn.div
            · apply continuousOn_const
            · apply hwc.continuousOn
            · intro u hu
              rw [Set.uIcc_of_le ht.1] at hu
              grind
        have hG_inv : ∀ t ∈ Set.Icc (0 : ℝ) T, x t ≤ G⁻¹ (G x0 + ∫ s in 0..t, g s)  := by
          intro t ht
          have hG_deriv : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt G (1 / w u) u := by
            intro u hu
            have hw_pos : w u > 0 := hwb u (by grind)
            have hw_cont : ContinuousAt w u := hwc.continuousAt
            have hw_ne_zero : w u ≠ 0 := by linarith
            have h_inv_cont : ContinuousAt (fun x => (w x)⁻¹) u := by
              apply ContinuousAt.inv₀ <;> assumption
            have hG_deriv : HasDerivAt (fun x => ∫ t in u₀..x, 1 / w t) (1 / w u) u := by
              apply intervalIntegral.integral_hasDerivAt_right
              · apply ContinuousOn.intervalIntegrable
                apply ContinuousOn.div
                · apply continuousOn_const
                · exact hwc.continuousOn
                · intro x hx
                  have hx_in : x ∈ Set.Ioi (0 : ℝ) := by sorry
                  grind
              · have h_meas : Measurable (fun x ↦ 1 / w x) := Measurable.div measurable_const hwc.measurable
                exact h_meas.stronglyMeasurable.stronglyMeasurableAtFilter
              · grind
            exact hG_deriv
          have hG_eq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ u in (x 0)..(x t), 1 / w u = G (x t) - G (x 0)  := by
              intro t ht
              apply intervalIntegral.integral_eq_sub_of_hasDerivAt
              · sorry
              · sorry
          have hG_sub : ∀ t ∈ Set.Icc (0 : ℝ) T, G (x t) - G (x 0) ≤ ∫ s in 0..t, g s := by
            intro t ht
            rw [← hG_eq]
            specialize hx_subst t ht
            grind
          have hGinv_mul : ∀ t ∈ Set.Icc (0 : ℝ) T, G⁻¹ (G x0 + ∫ s in 0..t, g s) ≥  G⁻¹ (G (x t) - G (x 0) + G x0) := by
            intro t ht
            rw [← hG_eq]
            sorry



        exact hG_inv



#check lt_of_lt_of_le
