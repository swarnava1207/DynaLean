import Mathlib
import DynaLean.Defs


variable {f : ℝ → ℝ → ℝ}

namespace ODE

/-- Bihari-type upper bound obtained by transforming the differential inequality
with the integral of the reciprocal comparison function. -/
theorem nonneg_integral_bound {ε : NNReal} (hε : 0 < ε) (g : ℝ → ℝ)
      (hfc : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (hgc : Continuous g)
      (w : ℝ → ℝ) (hwc : Continuous w) (x : ℝ → ℝ) (u₀ : ℝ)
      (hu₀ : u₀ ∈ Set.Ici (0 : ℝ))
      (hx : SolutionExists f x0 x (0 : ℝ) T (Set.Icc (-(ε : ℝ)) (T+ ε)))
      (hfb : (∀ t ∈ Set.Icc (0 : ℝ) T, f t (x t) ≤ g t * w (x t)))
      (hwb : ∀ u ∈ Set.Ici (0 : ℝ), w u > 0)
      (hxb : ∀ t ∈ Set.Icc (0 : ℝ) T, x t ≥ 0)
      (hdg : (∀ u : ℝ , G u = ∫ t in u₀..u, 1 / w t) ∧
      (∀ t : ℝ, (G x0 + ∫ s in 0..t, g s) ∈ G '' (Set.Ici (0 : ℝ)))) :
      (∃ G_inv : ℝ → ℝ, (∀ u ∈ Set.Ici (0 : ℝ), G_inv (G u) = u) ∧
      (∀ v ∈ G '' (Set.Ici (0 : ℝ)), G (G_inv v) = v) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, x t ≤ G_inv (G x0 + ∫ s in 0..t, g s))) := by
      let ⟨hG_def, hG_range⟩ := hdg
      have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      have hx_deriv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt x (f t (x t)) t := by
        intro t ht
        refine (hx.2 t ht).hasDerivAt (Icc_mem_nhds ?_ ?_)
        · linarith [ht.1]
        · linarith [ht.2]
      have hx_cont_T : ContinuousOn x (Set.Icc (0 : ℝ) T) := fun u hu =>
        (hx_deriv u hu).continuousAt.continuousWithinAt
      use G.invFunOn (Set.Ici (0 : ℝ))
      have hG_strict_mono : StrictMonoOn G (Set.Ici 0) := by
          unfold StrictMonoOn
          intro a ha b hb hab
          have : (∫ t in u₀..b, 1 / w t) - ∫ t in u₀..a, 1 / w t = ∫ t in a..b, 1 / w t := by
            apply intervalIntegral.integral_interval_sub_left
            · apply ContinuousOn.intervalIntegrable
              apply ContinuousOn.div continuousOn_const hwc.continuousOn
              intro x hx
              have : x ≥ 0 := by
                apply le_trans (le_min hu₀ hb) hx.1
              grind
            · apply ContinuousOn.intervalIntegrable
              apply ContinuousOn.div continuousOn_const hwc.continuousOn
              intro x hx
              have : x ≥ 0 := by
                apply le_trans (le_min hu₀ ha) hx.1
              grind
          have h_integral_pos : ∫ t in a..b, 1 / w t > 0 := by
            apply intervalIntegral.intervalIntegral_pos_of_pos_on
            · apply ContinuousOn.intervalIntegrable
              apply ContinuousOn.div continuousOn_const hwc.continuousOn
              intro x hx
              have : x ≥ 0 := by
                apply le_trans (le_min ha hb) hx.1
              grind
            · intro x hx
              have : x > 0 := by
                apply lt_of_le_of_lt ha hx.1
              specialize hwb x (by grind)
              exact one_div_pos.2 hwb
            · grind
          grind
      have hG_inj : Set.InjOn G (Set.Ici 0) := hG_strict_mono.injOn
      have hG_inv_mono : MonotoneOn (Function.invFunOn G (Set.Ici 0)) (G '' Set.Ici 0) := by
          rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
          rw [Set.InjOn.leftInvOn_invFunOn hG_inj ha, Set.InjOn.leftInvOn_invFunOn hG_inj hb]
          exact (hG_strict_mono.le_iff_le ha hb).mp hab
      have hx_left : ∀ u ∈ Set.Ici 0, Function.invFunOn G (Set.Ici 0) (G u) = u := by
        intro u hu
        apply Set.InjOn.leftInvOn_invFunOn hG_inj hu
      constructor
      · exact hx_left
      · constructor
        · intro v hv
          exact G.invFunOn_eq hv
        · intro t ht
          have hx_div : ∀ t ∈ Set.Ioc (0 : ℝ) T, f t (x t) / w (x t) ≤ g t := by
            intro t ht
            specialize hfb t (by grind)
            specialize hxb t (by grind)
            specialize hwb (x t) (by grind)
            rw [div_le_iff₀' hwb]
            grind
          have hx_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫ s in 0..t, f s (x s) / w (x s) ≤ ∫ s in 0..t, g s := by
            intro t ht
            apply intervalIntegral.integral_mono_on_of_le_Ioo ht.1
            · have hx_cont : ContinuousOn x (Set.Icc 0 t) :=
                hx_cont_T.mono (Set.Icc_subset_Icc le_rfl ht.2)
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
          have hx_subst : ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫ u in (x 0)..(x t), 1 / w u ≤ ∫ s in 0..t, g s := by
            intro t ht
            let k := fun x => 1 / w x
            have : ∫ u in (x 0)..(x t), 1 / w u = ∫ u in (x 0)..(x t), k u := by grind
            rw [this]
            rw [← intervalIntegral.integral_comp_mul_deriv']
            · specialize hx_int t ht
              have : ∀ s ∈ Set.Icc (0 : ℝ) T, f s (x s) / w (x s) = 1 / w (x s) * f s (x s) :=
                by intro s hs; rw [div_eq_mul_one_div]; grind
              have hint_eq :
              ∫ (s : ℝ) in 0..t, f s (x s) / w (x s) = ∫ (s : ℝ) in 0..t, (k ∘ x) s * f s (x s)
                := by
                apply intervalIntegral.integral_congr
                intro s hs
                rw [Set.uIcc_of_le ht.1] at hs
                have hs_T : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
                exact this s hs_T
              rw [hint_eq] at hx_int
              exact hx_int
            · intro m hm
              rw [Set.uIcc_of_le ht.1] at hm
              exact hx_deriv m ⟨hm.1, le_trans hm.2 ht.2⟩
            · have hx_cont : ContinuousOn x (Set.Icc 0 t) :=
                hx_cont_T.mono (Set.Icc_subset_Icc le_rfl ht.2)
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
          let G_inv := G.invFunOn (Set.Ici (0 : ℝ))
          have hG_inv : ∀ t ∈ Set.Icc (0 : ℝ) T, x t ≤ G_inv (G x0 + ∫ s in 0..t, g s)  := by
            intro t ht
            -- note: `Set.Ici`, not `Set.Ioi` — we need the derivative at `0` as well,
            -- since `x 0` may be `0`.
            have hG_deriv : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt G (1 / w u) u := by
              intro u hu
              have hw_pos : w u > 0 := hwb u hu
              have hw_cont : ContinuousAt w u := hwc.continuousAt
              have hw_ne_zero : w u ≠ 0 := by linarith
              have h_inv_cont : ContinuousAt (fun y => 1 / w y) u :=
                continuousAt_const.div hw_cont hw_ne_zero
              have hG_deriv : HasDerivAt (fun y => ∫ t in u₀..y, 1 / w t) (1 / w u) u := by
                apply intervalIntegral.integral_hasDerivAt_right
                · apply ContinuousOn.intervalIntegrable
                  apply ContinuousOn.div continuousOn_const hwc.continuousOn
                  intro y hy
                  have hy_in : (0 : ℝ) ≤ y := le_trans (le_min hu₀ hu) hy.1
                  exact ne_of_gt (hwb y hy_in)
                · have h_meas : Measurable (fun y ↦ 1 / w y)
                    := Measurable.div measurable_const hwc.measurable
                  exact h_meas.stronglyMeasurable.stronglyMeasurableAtFilter
                · exact h_inv_cont
              have hGeq : G = fun y => ∫ t in u₀..y, 1 / w t := funext hG_def
              rw [hGeq]
              exact hG_deriv
            have hG_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∫ u in (x 0)..(x t), 1 / w u = G (x t) - G (x 0) := by
                intro t ht
                have hx0 : (0 : ℝ) ≤ x 0 := hxb 0 ⟨le_rfl, le_trans ht.1 ht.2⟩
                have hxt : (0 : ℝ) ≤ x t := hxb t ht
                have hsub : ∀ u ∈ Set.uIcc (x 0) (x t), u ∈ Set.Ici (0 : ℝ) := by
                  intro u hu
                  exact le_trans (le_min hx0 hxt) hu.1
                apply intervalIntegral.integral_eq_sub_of_hasDerivAt
                · intro u hu
                  exact hG_deriv u (hsub u hu)
                · apply ContinuousOn.intervalIntegrable
                  apply ContinuousOn.div continuousOn_const hwc.continuousOn
                  intro u hu
                  exact ne_of_gt (hwb u (hsub u hu))
            have hG_sub : ∀ t ∈ Set.Icc (0 : ℝ) T, G (x t) - G (x 0) ≤ ∫ s in 0..t, g s := by
              intro t ht
              rw [← hG_eq t ht]
              specialize hx_subst t ht
              grind
            have hGinv_mul : ∀ t ∈ Set.Icc (0 : ℝ) T,
            G_inv (G x0 + ∫ s in 0..t, g s) ≥  G_inv (G (x t) - G (x 0) + G x0) := by
              intro t ht
              rw [← hG_eq]
              · have eq :
                (∫ u in x 0..x t, 1 / w u) + G x0 = G (x t) - G (x 0) + G x0 := by rw [← hG_eq t ht]
                have : x0 = x 0 := by simp only [hx.1]
                rw [this] at eq
                simp only [sub_add_cancel] at eq
                by_cases h_case : ∫ s in 0..t, g s = G (x t) - G (x 0)
                · grind
                · apply monotoneOn_iff_forall_lt.mp hG_inv_mono
                  · rw [this,eq]
                    grind
                  · specialize hG_range t
                    grind
                  · grind
              · grind
            have hG_inv_eq : ∀ t ∈ Set.Ioc (0 : ℝ) T, G_inv (G (x t) - G (x 0) + G x0) = x t := by
              intro t ht
              have : x0 = x 0 := by simp only [hx.1]
              rw [this]
              simp only [sub_add_cancel]
              specialize hx_left (x t) (by grind)
              grind
            by_cases h_case : t = 0
            · rw [h_case]
              simp only [intervalIntegral.integral_same, add_zero, ge_iff_le]
              rw [← hx.1]
              grind
            · specialize hG_inv_eq t (by grind)
              grind
          specialize hG_inv t ht
          grind

end ODE
