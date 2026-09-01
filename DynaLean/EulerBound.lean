import Mathlib
import DynaLean.Defs
import DynaLean.EulerScheme
open Topology

namespace ODE


theorem taylor_upto_two (y : ℝ → ℝ) (hcont : ContDiffOn ℝ 1 y (Set.uIcc t (t + k)))
                        (hk : k ≠ 0)
                        (hy' : DifferentiableOn ℝ (iteratedDerivWithin 1 y (Set.uIcc t (t + k)))
                        (Set.uIoo t (t + k))) :
      ∃ c ∈ Set.uIcc t (t + k), y (t + k)
      = y t + iteratedDerivWithin 1 y (Set.uIcc t (t + k)) t * k
            + iteratedDerivWithin 2 y (Set.uIcc t (t + k)) c * k^2 / 2 := by
            have tk : t ≠ t + k := by grind
            let ⟨c, hc⟩ := taylor_mean_remainder_lagrange (f := y) (n := 1) tk hcont hy'
            use c
            constructor
            · apply Set.uIoo_subset_uIcc_self; exact hc.1
            · let htaylor := hc.2
              rw [taylorWithinEval_succ] at htaylor
              rw [taylor_within_zero_eval] at htaylor
              simp only [CharP.cast_eq_zero, zero_add, Nat.factorial_zero, Nat.cast_one, mul_one,
                inv_one, add_sub_cancel_left, pow_one, one_mul, iteratedDerivWithin_one,
                smul_eq_mul, Nat.reduceAdd] at htaylor
              simp only [Nat.factorial_succ, Nat.factorial_zero] at htaylor
              simp only [Nat.reduceAdd, zero_add, mul_one, Nat.cast_ofNat] at htaylor
              rw [← htaylor]
              simp only [iteratedDerivWithin_one]
              grind

variable {f : ℝ → ℝ → ℝ} {x0 : ℝ} {T : ℚ}

theorem euler_bound_solution (y : ℝ → ℝ) (K : NNReal) (M : ℚ) (hMne : M > 0)
      (hx : ∀ a b : ℝ, SolutionExists f x0 y a b (Set.Icc a b))
      (hcont : ContDiff ℝ 2 y) (t₀ : ℝ)
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t, |iteratedDeriv 2 y t| ≤ M)
      (S : Scheme) (hS : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0)
      (hy': Differentiable ℝ (iteratedDeriv 1 y)) :
      ∀ n ∈ Finset.range (Nat.floor (T / S.δ)),
       |y (S.t n) - S.x n| ≤ (S.t n - S.t₀) * (ε + M * S.δ/2) *
            (Real.exp (K * (S.t n - S.t₀))) := by
      have hε : 0 ≤ ε := le_trans (b := |f 0 0 - m 0 0|) (by grind) (by exact_mod_cast hf 0 0)
      set e := fun n => |y (S.t n) - S.x n| with heq
      intro n hn
      have hmain : ∀ i : ℕ, e (i + 1) ≤ e i * (1 + K * S.δ) + (ε + M * S.δ/2) * S.δ := by
        intro i
        rw [heq]
        simp only
        have hne : (S.δ : ℝ) ≠ 0 := by rw [Rat.cast_ne_zero]; exact S.hδ.ne'
        have hy'' : DifferentiableOn ℝ (iteratedDerivWithin 1 y (Set.uIcc (S.t i) (S.t i + S.δ)))
                        (Set.uIoo (S.t i) (S.t i + S.δ)) := by
            rw [iteratedDerivWithin_one]
            have hδR : (0:ℝ) < ((S.δ : ℚ) : ℝ) := by exact_mod_cast S.hδ
            have hab : ((S.t i : ℚ) : ℝ) ≤ ((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) := by linarith
            have huIcc : Set.uIcc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))
            = Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)) :=
            Set.uIcc_of_le hab
            have hIoo : Set.uIoo ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))
            = Set.Ioo ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)) :=
            Set.uIoo_of_le hab
            have hy1 : Differentiable ℝ (deriv y) := by
                  rw [← iteratedDeriv_one]; exact hy'
            refine DifferentiableOn.congr (f := deriv y) hy1.differentiableOn ?_
            intro x hx
            rw [hIoo] at hx
            exact derivWithin_of_mem_nhds (by rw [huIcc]; exact Icc_mem_nhds hx.1 hx.2)
        have hcont' : ContDiff ℝ 1 y := hcont.of_le (by decide)
        let ⟨c, hc, hcp⟩ := taylor_upto_two (t := S.t i) (k := S.δ) y (hcont := hcont'.contDiffOn)
                           hne hy''
        have hderiv : derivWithin y (Set.uIcc (S.t i) (S.t i + S.δ)) (S.t i) = f (S.t i) (y (S.t i))
            := by
            rw [DifferentiableAt.derivWithin]
            · have hmem : (S.t i : ℝ) ∈ Set.Icc ((S.t i : ℝ) - 1) ((S.t i : ℝ) + 1) :=
                  ⟨by linarith, by linarith⟩
              have hnhds : Set.Icc ((S.t i : ℝ) - 1) ((S.t i : ℝ) + 1) ∈ nhds (S.t i : ℝ) :=
                  Icc_mem_nhds (by linarith) (by linarith)
              obtain ⟨-, hsol⟩ := hx ((S.t i : ℝ) - 1) ((S.t i : ℝ) + 1)
              exact ((hsol _ hmem).hasDerivAt hnhds).deriv
            · exact hcont.differentiable (by simp) |>.differentiableAt
            · have hδR : (0:ℝ) < (S.δ : ℝ) := by exact_mod_cast S.hδ
              have hab : (S.t i : ℝ) < (S.t i : ℝ) + (S.δ : ℝ) := by linarith
              rw [Set.uIcc_of_le hab.le]
              exact uniqueDiffOn_Icc hab _ (Set.left_mem_Icc.mpr hab.le)
        calc
            |y (S.t (i + 1)) - S.x (i + 1)|
                  = |y (S.t i + S.δ) - (S.x i + S.δ * S.m (S.t i) (S.x i))| := by
                    rw [Scheme.t_succ, Scheme.x_succ]; push_cast; ring
            _ = |y (S.t i) + iteratedDerivWithin 1 y (Set.uIcc (S.t i) (S.t i + S.δ)) (S.t i) * S.δ
                  + iteratedDerivWithin 2 y (Set.uIcc (S.t i) (S.t i + S.δ)) c * S.δ^2 / 2
                  - (S.x i + S.δ * S.m (S.t i) (S.x i))| := by rw [hcp]
            _ = |y (S.t i) + derivWithin y (Set.uIcc (S.t i) (S.t i + S.δ)) (S.t i) * S.δ
                  + iteratedDerivWithin 2 y (Set.uIcc (S.t i) (S.t i + S.δ)) c * S.δ^2 / 2
                  - (S.x i + S.δ * S.m (S.t i) (S.x i))| := by
                    simp only [iteratedDerivWithin_one]
            _ = |y (S.t i) + f (S.t i) (y (S.t i)) * S.δ
                  + iteratedDerivWithin 2 y (Set.uIcc (S.t i) (S.t i + S.δ)) c * S.δ^2 / 2
                  - (S.x i + S.δ * S.m (S.t i) (S.x i))| := by rw [hderiv]
            _ = |y (S.t i) + f (S.t i) (y (S.t i)) * S.δ
                  - (S.x i + S.δ * S.m (S.t i) (S.x i))
                  + iteratedDeriv 2 y c * S.δ^2 / 2| := by
                        rw [iteratedDerivWithin_eq_iteratedDeriv _ _ hc]
                        · ring_nf
                        · have hδR : (0:ℝ) < (S.δ : ℝ) := by exact_mod_cast S.hδ
                          have hab : (S.t i : ℝ) < (S.t i : ℝ) + (S.δ : ℝ) := by linarith
                          rw [Set.uIcc_of_le hab.le]
                          exact uniqueDiffOn_Icc hab
                        · exact hcont.contDiffAt
            _ ≤ |y (S.t i) + f (S.t i) (y (S.t i)) * S.δ
                  - (S.x i + S.δ * S.m (S.t i) (S.x i))|
                  + |iteratedDeriv 2 y c * S.δ^2 / 2| := by
                    apply abs_add_le
            _ ≤ |(y (S.t i) - S.x i) + S.δ * (f (S.t i) (y (S.t i)) - S.m (S.t i) (S.x i))|
                  + |iteratedDeriv 2 y c * S.δ^2 / 2| := by
                  grind
            _ ≤ |y (S.t i) - S.x i| + |S.δ * (f (S.t i) (y (S.t i)) - S.m (S.t i) (S.x i))|
                  + |iteratedDeriv 2 y c * S.δ^2 / 2| := by
                    grind
            _ ≤ |y (S.t i) - S.x i| + S.δ * |f (S.t i) (y (S.t i)) - S.m (S.t i) (S.x i)|
                  + |iteratedDeriv 2 y c * S.δ^2 / 2| := by
                    apply add_le_add_left
                    apply add_le_add_right
                    rw [abs_mul]
                    rw [abs_of_pos (by exact_mod_cast S.hδ)]
            _ ≤ |y (S.t i) - S.x i| + S.δ * (|f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)
                  + f (S.t i) (S.x i) - S.m (S.t i) (S.x i)|)
                  + |iteratedDeriv 2 y c * S.δ^2 / 2| := by
                    apply add_le_add_left
                    apply add_le_add_right
                    grind
            _ ≤ |y (S.t i) - S.x i| + S.δ * (|f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)|
                  + |f (S.t i) (S.x i) - S.m (S.t i) (S.x i)|)
                  + |iteratedDeriv 2 y c * S.δ^2 / 2| := by
                    apply add_le_add_left
                    apply add_le_add_right
                    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast S.hδ.le)
                    grind
            _ ≤ |y (S.t i) - S.x i| + S.δ * (K * |y (S.t i) - S.x i| + ε)
                  + |iteratedDeriv 2 y c * S.δ^2 / 2| := by
                  apply add_le_add_left
                  apply add_le_add_right
                  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast S.hδ.le)
                  apply add_le_add
                  · specialize hK (S.t i)
                    set g := fun x => f (S.t i) x with hg
                    have hg' : ∀ x , g x = f (S.t i) x := by grind
                    rw [← hg', ← hg']
                    simp only [← Real.dist_eq]
                    exact hK.dist_le_mul (y (S.t i)) (S.x i)
                  · rw [hS.1]
                    exact hf (S.t i) (S.x i)
            _ ≤ |y (S.t i) - S.x i| + S.δ * (K * |y (S.t i) - S.x i| + ε)
                  + M * S.δ^2 / 2 := by
                    rw [add_assoc, add_assoc]
                    apply add_le_add_right
                    apply add_le_add_right
                    specialize hM c
                    field_simp; ring_nf
                    rw [abs_mul]; simp only [abs_mul, abs_pow, sq_abs, one_div, abs_inv,
                      Nat.abs_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                      inv_mul_cancel_right₀]
                    rw [mul_comm]
                    apply mul_le_mul_of_nonneg_left hM
                    exact pow_two_nonneg (S.δ : ℝ)
            _ = |y (S.t i) - S.x i| * (1 + S.δ * K) + (ε + M * S.δ / 2) * S.δ := by
                    grind
            _ = e i * (1 + K * S.δ) + (ε + M * S.δ/2) * S.δ := by
                  rw [heq]
                  simp only [add_left_inj, mul_eq_mul_left_iff, add_right_inj, abs_eq_zero]
                  apply Or.inl; grind
      have heq' : e n = |y (S.t n) - S.x n| := by grind
      rw [← heq']
      have he0 : e 0 = 0 := by
        rw [heq]
        simp only [Scheme.t_zero, Scheme.x_zero]
        specialize hx (S.t₀) (S.t₀ + 1)
        rw [hx.1]
        grind
      calc
        e n ≤ (e 0 + ∑ k ∈ Finset.Ico 0 n, (S.δ*(ε + M * S.δ/2) : ℝ))
                  * Real.exp (∑ i ∈ Finset.Ico 0 n, K * S.δ) := by
                  apply discrete_gronwall (n := n) (u := e) (n₀ := 0) (hun₀ := he0.ge)
                        (b := fun i => S.δ * (ε + M * S.δ/2)) (c := fun i => K * S.δ)
                        (hn := (by grind)) _ _ _
                  · intro j hj
                    specialize hmain j
                    grind
                  · intro j hj
                    apply mul_nonneg (NNReal.coe_nonneg K)
                    exact_mod_cast S.hδ.le
                  · intro j hj
                    apply mul_nonneg
                    · exact_mod_cast S.hδ.le
                    · apply add_nonneg (by exact_mod_cast hε)
                      apply mul_nonneg _ (by grind)
                      apply mul_nonneg (by exact_mod_cast hMne.le) (by exact_mod_cast S.hδ.le)
        _ = (e 0 + (S.δ*(ε + M * S.δ/2) : ℝ) * n)
                  * Real.exp (K * S.δ * n) := by
                  rw [Finset.sum_const, Finset.sum_const]
                  have hcard : (n : ℝ) = Finset.card (Finset.Ico 0 n) := by
                        simp only [Nat.Ico_zero_eq_range,
                    Finset.card_range]
                  grind
        _ = (S.δ*(ε + M * S.δ/2) : ℝ) * n * Real.exp (K * S.δ * n) := by
                  rw [he0, zero_add]
        _ = (n * S.δ : ℝ) * (ε + M * S.δ/2) * Real.exp (K * (n * S.δ : ℝ)) := by grind
        _ = (S.t n - S.t₀) * (ε + M * S.δ/2) * (Real.exp (K * (S.t n - S.t₀))) := by
            have htn : (S.t n - S.t₀) = (n * S.δ : ℝ) := by
                        rw [Scheme.t_succ']
                        push_cast
                        simp only [add_sub_cancel_left]
            rw [← htn]

end ODE
