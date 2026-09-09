import Mathlib
import DynaLean.Defs
import DynaLean.EulerScheme
open Topology

namespace ODE

/-- Taylor's theorem with a first-order term and a second-order remainder. -/
theorem taylor_upto_two (y : ℝ → ℝ) (hcont : ContDiffOn ℝ 1 y (Set.uIcc t (t + k)))
                        (hk : k ≠ 0)
                        (hy' : DifferentiableOn ℝ (iteratedDerivWithin 1 y (Set.uIcc t (t + k)))
                        (Set.uIoo t (t + k))) :
      ∃ c ∈ Set.uIoo t (t + k), y (t + k)
      = y t + iteratedDerivWithin 1 y (Set.uIcc t (t + k)) t * k
            + iteratedDerivWithin 2 y (Set.uIcc t (t + k)) c * k^2 / 2 := by
            have tk : t ≠ t + k := by grind
            obtain ⟨c, hc⟩ := taylor_mean_remainder_lagrange (f := y) (n := 1) tk hcont hy'
            refine ⟨c, hc.1, ?_⟩
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

variable {f : ℝ → ℝ → ℝ} {x0 : ℚ} {t₀ T : ℚ}

/-- Bound the global Euler error by accumulating local truncation and model errors. -/
theorem euler_bound_solution (y : ℝ → ℝ) (K : NNReal) (M : ℚ) (hMne : M > 0)
      (hT : t₀ < T)
      (hx : SolutionExists f (x0 : ℝ) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ), |iteratedDeriv 2 y t| ≤ (M : ℝ))
      (S : Scheme) (hS : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0) :
      ∀ n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1),
       |y (S.t n) - S.x n| ≤ (S.t n - S.t₀) * (ε + M * S.δ/2) *
            (Real.exp (K * (S.t n - S.t₀))) := by
      set N : ℕ := ⌊(T - S.t₀) / S.δ⌋₊ with hNdef
      have hε : 0 ≤ ε := le_trans (b := |f 0 0 - m 0 0|) (by grind) (by exact_mod_cast hf 0 0)
      -- grid points, in ℚ
      have htQ : ∀ j : ℕ, S.t j = t₀ + (j : ℚ) * S.δ := by
        intro j; rw [Scheme.t_succ', hS.2.1]
      have hqnn : (0 : ℚ) ≤ (T - S.t₀) / S.δ := by
        rw [hS.2.1]; exact div_nonneg (by linarith) S.hδ.le
      have hle : ∀ j : ℕ, j ≤ N → S.t j ≤ T := by
        intro j hj
        rw [hNdef] at hj
        have h1 : ((j : ℕ) : ℚ) ≤ (T - S.t₀) / S.δ := (Nat.le_floor_iff hqnn).mp hj
        rw [hS.2.1] at h1
        have h2 : (j : ℚ) * S.δ ≤ T - t₀ := (le_div_iff₀ S.hδ).mp h1
        rw [htQ]; linarith
      have hge : ∀ j : ℕ, t₀ ≤ S.t j := by
        intro j
        have : (0 : ℚ) ≤ (j : ℚ) * S.δ := mul_nonneg (by positivity) S.hδ.le
        rw [htQ]; linarith
      set e := fun n => |y (S.t n) - S.x n| with heq
      intro n hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hmain : ∀ i ∈ Finset.range N,
          e (i + 1) ≤ e i * (1 + K * S.δ) + (ε + M * S.δ/2) * S.δ := by
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        rw [heq]
        simp only
        have hne : (S.δ : ℝ) ≠ 0 := by rw [Rat.cast_ne_zero]; exact S.hδ.ne'
        have hδR : (0 : ℝ) < ((S.δ : ℚ) : ℝ) := by exact_mod_cast S.hδ
        have hab : ((S.t i : ℚ) : ℝ) < ((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) := by linarith
        -- the step interval sits inside `[t₀, T]`
        have hstep : (S.t i : ℚ) + S.δ = S.t (i + 1) := by
          rw [htQ, htQ]; push_cast; ring
        have hti : ((t₀ : ℚ) : ℝ) ≤ ((S.t i : ℚ) : ℝ) := by exact_mod_cast hge i
        have htiT : ((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) ≤ ((T : ℚ) : ℝ) := by
          have h := hle (i + 1) (by omega)
          rw [← hstep] at h
          exact_mod_cast h
        have hIcc : Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))
            ⊆ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := Set.Icc_subset_Icc hti htiT
        have hIuIcc : Set.uIcc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))
            ⊆ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := by
          rw [Set.uIcc_of_le hab.le]; exact hIcc
        -- `y'` is differentiable on the interior of the step, from `ContDiffOn ℝ 2`
        have hd1 : ContDiffOn ℝ 1
            (derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))))
            (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) :=
          (hcont.mono hIcc).derivWithin (uniqueDiffOn_Icc hab) (by decide)
        have hy'' : DifferentiableOn ℝ
            (iteratedDerivWithin 1 y
              (Set.uIcc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))))
            (Set.uIoo ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) := by
          rw [iteratedDerivWithin_one, Set.uIcc_of_le hab.le, Set.uIoo_of_le hab.le]
          exact (hd1.differentiableOn one_ne_zero).mono Set.Ioo_subset_Icc_self
        obtain ⟨c, hc, hcp⟩ :=
          taylor_upto_two (t := ((S.t i : ℚ) : ℝ)) (k := ((S.δ : ℚ) : ℝ)) y
            (hcont := (hcont.mono hIuIcc).of_le (by decide)) hne hy''
        -- the mean value point is interior, hence interior to `[t₀, T]`
        have hc' : c ∈ Set.Ioo ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)) := by
          rwa [Set.uIoo_of_le hab.le] at hc
        have hcT : c ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) :=
          ⟨lt_of_le_of_lt hti hc'.1, lt_of_lt_of_le hc'.2 htiT⟩
        have hcCD : ContDiffAt ℝ 2 y c := hcont.contDiffAt (Icc_mem_nhds hcT.1 hcT.2)
        -- the Euler direction really is `derivWithin y` at the left endpoint
        have hderiv : derivWithin y (Set.uIcc (S.t i) (S.t i + S.δ)) (S.t i)
            = f (S.t i) (y (S.t i)) := by
            have hmem : ((S.t i : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) :=
              ⟨hti, by linarith⟩
            rw [Set.uIcc_of_le hab.le]
            exact ((hx.2 _ hmem).mono hIcc).derivWithin
              (uniqueDiffOn_Icc hab _ (Set.left_mem_Icc.mpr hab.le))
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
                        rw [iteratedDerivWithin_eq_iteratedDeriv _ _
                              (Set.uIoo_subset_uIcc_self hc)]
                        · ring_nf
                        · rw [Set.uIcc_of_le hab.le]
                          exact uniqueDiffOn_Icc hab
                        · exact hcCD
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
                    have hM : |iteratedDeriv 2 y c| ≤ (M : ℝ) := hM c hcT
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
      ----------------------------------------------------------------
      -- Grönwall.  `discrete_gronwall` wants the recurrence at *every* index, but
      -- `hmain` only holds while the grid stays in `[t₀, T]`.  So freeze the sequence
      -- at `N`: past `N` the recurrence is trivial because `b, c ≥ 0` and `e N ≥ 0`.
      ----------------------------------------------------------------
      have heq' : e n = |y (S.t n) - S.x n| := by simp only [heq]
      have he0 : e 0 = 0 := by
        rw [heq]
        simp only [Scheme.t_zero, Scheme.x_zero, hS.2.1, hS.2.2]
        rw [hx.1]
        simp
      have hepos : ∀ j, 0 ≤ e j := by
        intro j; simp only [heq]; exact abs_nonneg _
      have hδ0 : (0 : ℝ) ≤ (S.δ : ℝ) := by exact_mod_cast S.hδ.le
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMne.le
      have hcnn : (0 : ℝ) ≤ (K : ℝ) * (S.δ : ℝ) := mul_nonneg (NNReal.coe_nonneg K) hδ0
      have hbnn : (0 : ℝ) ≤ (S.δ : ℝ) * (ε + (M : ℝ) * (S.δ : ℝ) / 2) := by
        have h2 : (0 : ℝ) ≤ (M : ℝ) * (S.δ : ℝ) / 2 :=
          div_nonneg (mul_nonneg hM0 hδ0) (by norm_num)
        exact mul_nonneg hδ0 (by linarith)
      set u : ℕ → ℝ := fun j => e (min j N) with hu_def
      have hrec : ∀ j ≥ 0, u (j + 1) ≤ (1 + (K : ℝ) * S.δ) * u j + S.δ * (ε + M * S.δ / 2) := by
        intro j _
        rcases Nat.lt_or_ge j N with hjN | hjN
        · have h1 : min (j + 1) N = j + 1 := by omega
          have h2 : min j N = j := by omega
          simp only [hu_def, h1, h2]
          have h := hmain j (Finset.mem_range.mpr hjN)
          ring_nf at h ⊢
          linarith
        · have h1 : min (j + 1) N = N := by omega
          have h2 : min j N = N := by omega
          simp only [hu_def, h1, h2]
          have h3 : (0 : ℝ) ≤ (K : ℝ) * (S.δ : ℝ) * e N := mul_nonneg hcnn (hepos N)
          nlinarith [hbnn, h3]
      have hmin0 : min 0 N = 0 := by omega
      have hminn : min n N = n := by omega
      have hu0 : u 0 = 0 := by simp only [hu_def, hmin0]; exact he0
      have hun : u n = e n := by simp only [hu_def, hminn]
      have hfin := discrete_gronwall (n₀ := 0) (u := u)
          (b := fun _ => (S.δ : ℝ) * (ε + (M : ℝ) * (S.δ : ℝ) / 2))
          (c := fun _ => (K : ℝ) * (S.δ : ℝ))
          hu0.ge hrec (fun j _ => hcnn) (fun j _ => hbnn) (Nat.zero_le n)
      simp only [Finset.sum_const, Nat.Ico_zero_eq_range, Finset.card_range,
        nsmul_eq_mul] at hfin
      rw [hu0, zero_add, hun] at hfin
      rw [← heq']
      refine hfin.trans (le_of_eq ?_)
      have htn : ((S.t n : ℚ) : ℝ) - ((S.t₀ : ℚ) : ℝ) = (n : ℝ) * (S.δ : ℝ) := by
        rw [Scheme.t_succ']
        push_cast
        simp only [add_sub_cancel_left]
      rw [htn, show (K : ℝ) * ((n : ℝ) * (S.δ : ℝ)) = (n : ℝ) * ((K : ℝ) * (S.δ : ℝ)) from by ring]
      ring


/-- Construct an Euler scheme whose final grid point is `T`. -/
def LastSchema (t₀ T : ℚ) (x0 : ℚ) (m : ℚ → ℚ → ℚ) (N : ℕ) (hN : N ≠ 0) (ht : t₀ < T) : Scheme where
  δ := (T - t₀) / N
  hδ := by
    have hN : (0 : ℚ) < N := by simp only [Nat.cast_pos]; grind
    have hTt : (0 : ℚ) < T - t₀ := by linarith
    have hdiv : (0 : ℚ) < (T - t₀) / N := by exact_mod_cast div_pos hTt hN
    exact_mod_cast hdiv
  t₀ := t₀
  x₀ := x0
  m := m


/-- Specialize the Euler error bound to a scheme ending exactly at `T`. -/
theorem euler_bound_solution_last (y : ℝ → ℝ) (K : NNReal) (M : ℚ) (hMne : M > 0)
      (hx : SolutionExists f (x0 : ℝ) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ), |iteratedDeriv 2 y t| ≤ (M : ℝ))
      (N : ℕ) (hN : N ≠ 0) (ht : t₀ < T)
      (S : Scheme) (hS : S = LastSchema t₀ T x0 m N hN ht) :
      |y T - S.pl T| ≤ (T - t₀) * (ε + M * S.δ/2) *
            (Real.exp (K * (T - t₀))) := by
      have hS' : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0 := by
        simp only [hS]
        constructor
        · rfl
        · constructor <;> rfl
      have h := euler_bound_solution (t₀ := t₀) y K M hMne ht hx hcont m hf hK hM S hS'
      have hTt : (0 : ℚ) < T - t₀ := by linarith
      have hNQ : ((N : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      have hδeq : S.δ = (T - t₀) / N := by rw [hS]; rfl
      have hdiv : (T - S.t₀) / S.δ = ((N : ℕ) : ℚ) := by
        rw [hS'.2.1, hδeq]
        field_simp
      have hfloor : ⌊(T - S.t₀) / S.δ⌋₊ = N := by rw [hdiv]; simp
      have hmemN : N ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1) := by
        rw [hfloor]; exact Finset.self_mem_range_succ N
      have htn : S.t N = T := by
            simp only [hS]
            simp only [Scheme.t_succ']
            simp only [LastSchema]
            field_simp
            ring
      calc
        _ = |y (S.t N) - S.pl (S.t N)| := by
          rw [htn]
        _ = |y (S.t N) - S.x N| := by
          simp only [Scheme.pl]
          rw [S.idx_eq_of_mem_Ico (n := N) (s := S.t N) (by grind) (by simp only [S.t_succ',
            Nat.cast_add, Nat.cast_one, add_lt_add_iff_left, S.hδ, mul_lt_mul_iff_left₀,
            lt_add_iff_pos_right, zero_lt_one])]
          simp [Scheme.lOn]
        _ ≤ (T - t₀) * (ε + M * S.δ/2) * (Real.exp (K * (T - t₀))) := by
          specialize h N hmemN
          rw [htn] at h
          have ht₀ : S.t₀ = t₀ := by simp only [hS]; rfl
          rw [ht₀] at h
          rwa [htn]

end ODE
