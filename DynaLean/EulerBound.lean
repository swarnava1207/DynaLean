module

public import Mathlib
public import DynaLean.Defs
public import DynaLean.EulerScheme

/-! # Error bounds for the Euler scheme

The central results of DynaLean. They bound the distance between an exact solution `y`
of `y' = f t y` and the Euler data produced by a `Scheme` (or `VectorScheme`), in terms
of three budgets:

* `ε` — the *model error*, `|f t x - m t x| ≤ ε`: how far the scheme's field is from
  the true one;
* `M` — a bound on `‖y''‖`, which controls the *local truncation error* of one Euler
  step (supplied by `DynaLean.Derivations`);
* `K` — a Lipschitz constant for `f` in its state argument, which controls how fast an
  error already committed is amplified by later steps.

## Shape of the development

1. `ODE.taylor_upto_two` and `ODE.taylor_lagrange_norm_bound_two` give the one-step
   Taylor estimate `‖y (t+k) - y t - k·y' t‖ ≤ (k²/2)·M`, in `ℝ` and in a Banach space
   respectively.
2. `ODE.euler_bound_solution_iterate` turns that into the *recurrence*
   `eₙ₊₁ ≤ eₙ (1 + Kδ) + (ε + Mδ/2) δ` for the grid-point error `eₙ`.
3. `ODE.euler_bound_solution` solves the recurrence crudely, with an `exp (K (t - t₀))`
   amplification factor; `ODE.euler_bound_solution_rational` solves it sharply via
   discrete Grönwall, giving the geometric-series form
   `(ε + Mδ/2) δ · ((1 + Kδ)ⁿ - 1) / (Kδ)`, which is rational in the data and so can be
   evaluated exactly.
4. `ODE.euler_bound_cell` extends a grid-point bound to *every* time inside a cell, and
   `ODE.euler_bound_solution_all` combines the two to bound `‖y s - interpolant s‖` at
   every `s ∈ [t₀, T]`.
5. `ODE.LastSchema` builds the scheme with `N` equal steps whose final grid point is
   exactly `T`, and `ODE.euler_bound_solution_last` specializes the bound to it.

Section `Vector` repeats steps 2-5 for `ℝ^k`-valued solutions; those are the versions
consumed by `DynaLean.DigitalTwin`.
-/

@[expose] public section
open Topology

namespace ODE

/-- Taylor's theorem with a first-order term and a second-order remainder.

The mean-value form: there is `c` strictly between `t` and `t + k` with
`y (t + k) = y t + y' t · k + y'' c · k² / 2`, where the derivatives are taken within
`uIcc t (t + k)`. Specialized from Mathlib's `taylor_mean_remainder_lagrange`. -/
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

open Set Filter Metric
open scoped Interval

open Set Filter Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Banach-space form of the second-order Taylor estimate: `‖y (t+k) - y t - k • y' t‖
≤ (k²/2) · M` whenever `‖y''‖ ≤ M` on `(t, t + k)`.

There is no mean-value theorem for vector-valued functions, so instead of
`ODE.taylor_upto_two` the proof writes the remainder as `∫ s in t..t+k, (y' s - y' t)`,
bounds the integrand by `M (s - t)` with the segment mean-value *inequality*, and
integrates. This is the estimate that governs the local truncation error of a single
Euler step, in both the scalar and the vector development. -/
theorem taylor_lagrange_norm_bound_two [CompleteSpace E]
    {y y' : ℝ → E} {y'' : ℝ → E}
    {t k M : ℝ} (hk : 0 ≤ k)
    (hy : ∀ s ∈ Icc t (t + k), HasDerivWithinAt y (y' s) (Icc t (t + k)) s)
    (hy_cont : ContinuousOn y' (Icc t (t + k)))
    (hy' : ∀ s ∈ Icc t (t + k), HasDerivWithinAt y' (y'' s) (Icc t (t + k)) s)
    (hM : ∀ s ∈ Ioo t (t + k), ‖y'' s‖ ≤ M) :
    ‖y (t + k) - y t - k • y' t‖ ≤ (k^2 / 2) * M := by
  have ht_le : t ≤ t + k := by linarith
  have h_stepA : ∀ s ∈ Icc t (t + k), ‖y' s - y' t‖ ≤ M * (s - t) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with hts | hts
    · simp [← hts]
    -- On `[a, t+k]` with `t < a`, the segment mean-value inequality only needs the
    -- derivative bound on `Ico a (t+k) ⊆ Ioo t (t+k)`.
    have key : ∀ a ∈ Ioo t s, ‖y' s - y' a‖ ≤ M * (s - a) := by
      intro a ha
      have hsub : Icc a (t + k) ⊆ Icc t (t + k) := Icc_subset_Icc ha.1.le le_rfl
      exact norm_image_sub_le_of_norm_deriv_le_segment'
        (f := y') (f' := y'') (a := a) (b := t + k) (C := M)
        (fun u hu => (hy' u (hsub hu)).mono hsub)
        (fun u hu => hM u ⟨lt_of_lt_of_le ha.1 hu.1, hu.2⟩)
        s ⟨ha.2.le, hs.2⟩
    -- Let `a → t⁺`; `y'` is continuous at `t` within `Icc t (t + k)`.
    have : (𝓝[Ioo t s] t).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT hts]; infer_instance
    have hsub' : Ioo t s ⊆ Icc t (t + k) := fun u hu => ⟨hu.1.le, hu.2.le.trans hs.2⟩
    have hF : Tendsto (fun a => ‖y' s - y' a‖) (𝓝[Ioo t s] t) (𝓝 ‖y' s - y' t‖) :=
      ((continuousWithinAt_const (b := y' s)).sub
        ((hy_cont t ⟨le_rfl, ht_le⟩).mono hsub')).norm
    have hG : Tendsto (fun a => M * (s - a)) (𝓝[Ioo t s] t) (𝓝 (M * (s - t))) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto t).mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hF hG (eventually_mem_nhdsWithin.mono key)
  have hmint : min t (t + k) = t := by grind
  have hmax : max t (t + k) = t + k := by grind
  have h_integrable_y' : IntervalIntegrable y' MeasureTheory.volume t (t + k) :=
    hy_cont.intervalIntegrable_of_Icc ht_le
  have hy_cont_y : ContinuousOn y (Icc t (t + k)) := fun s hs => (hy s hs).continuousWithinAt
  have h_ftc : ∫ s in t..(t + k), y' s = y (t + k) - y t := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht_le hy_cont_y
      (fun x hx => ?_) h_integrable_y'
    exact ((hy x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
  have h_const : ∫ _ in t..(t + k), y' t = k • y' t := by
    have h_eval := intervalIntegral.integral_const (y' t) (a := t) (b := t + k)
    have h_sub : (t + k) - t = k := by ring
    rw [h_sub] at h_eval
    exact h_eval
  have h_integrable_const : IntervalIntegrable (fun _ => y' t) MeasureTheory.volume t (t + k) :=
    intervalIntegrable_const
  have h_rem_eq : y (t + k) - y t - k • y' t = ∫ s in t..(t + k), (y' s - y' t) := by
    rw [← h_ftc, ← h_const, ← intervalIntegral.integral_sub h_integrable_y' h_integrable_const]
  rw [h_rem_eq]
  have h_norm_le : ‖∫ s in t..(t + k), (y' s - y' t)‖ ≤ ∫ s in t..(t + k), ‖y' s - y' t‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht_le
    · filter_upwards with s hs
      grind
    · have hcont : ContinuousOn (fun s => ‖y' s - y' t‖) (Icc t (t + k)) := by
        refine (hy_cont.sub continuousOn_const).norm
      exact hcont.intervalIntegrable_of_Icc ht_le
  have h_g_cont : Continuous (fun s : ℝ => M * (s - t)) := by continuity
  have h_g_int : IntervalIntegrable (fun s => M * (s - t)) MeasureTheory.volume t (t + k) :=
    h_g_cont.intervalIntegrable t (t + k)
  have h_diff_cont : ContinuousOn (fun s => ‖y' s - y' t‖) (Icc t (t + k)) := by
    refine (hy_cont.sub continuousOn_const).norm
  have h_diff_int : IntervalIntegrable (fun s => ‖y' s - y' t‖) MeasureTheory.volume t (t + k) :=
    h_diff_cont.intervalIntegrable_of_Icc ht_le
  have h_mono : (∫ s in t..(t + k), ‖y' s - y' t‖) ≤ ∫ s in t..(t + k), M * (s - t) := by
    refine intervalIntegral.integral_mono_on ht_le h_diff_int h_g_int (fun s hs => ?_)
    exact h_stepA s hs
  have h_eval_integral : (∫ s in t..(t + k), M * (s - t)) = (k^2 / 2) * M := by
    have h_antideriv : ∀ s ∈ [[t, t + k]],
        HasDerivAt (fun s => (M / 2) * (s - t)^2) (M * (s - t)) s := by
      intro s _
      have hd : HasDerivAt (fun s => (s - t)^2) (2 * (s - t)) s := by
        have h := (((hasDerivAt_id s).sub_const t).pow 2)
        simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one] at h
        apply HasDerivAt.congr_deriv h (by grind)
      have hd_mul := hd.const_mul (M / 2)
      have h_ring : (M / 2) * (2 * (s - t)) = M * (s - t) := by ring
      rw [h_ring] at hd_mul
      exact hd_mul
    have h_ant : ∀ s ∈ Icc t (t + k),
        deriv (fun s => (M / 2) * (s - t)^2) s = M * (s - t) := by
      intro s hs
      specialize h_antideriv s ⟨by rw [hmint]; exact hs.1, by rw [hmax]; exact hs.2⟩
      rw [h_antideriv.deriv]
    have h_int_eval := intervalIntegral.integral_deriv_eq_sub
      (fun s hs => (h_antideriv s hs).differentiableAt)
      (by
        apply IntervalIntegrable.congr _ h_g_int
        intro s hs
        simp only [h_ant s ⟨by rw [← hmint]; exact hs.1.le, by rw [← hmax]; exact hs.2.ge⟩]
        )
    simp only [add_sub_cancel_left,sub_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h_int_eval
    simp only [differentiableAt_const, deriv_const_mul_field', differentiableAt_fun_id,
      DifferentiableAt.fun_sub, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_fun_sub, deriv_id'', deriv_const', sub_zero, mul_one,
      intervalIntegral.integral_const_mul, intervalIntegral.intervalIntegrable_id,
      intervalIntegrable_const, intervalIntegral.integral_sub, integral_id,
      intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, mul_eq_mul_left_iff,
      div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] at h_int_eval
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.intervalIntegrable_id,
      intervalIntegrable_const, intervalIntegral.integral_sub, integral_id,
      intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul]
    simp only [sq]
    grind
  calc ‖∫ s in t..(t + k), (y' s - y' t)‖
    _ ≤ ∫ s in t..(t + k), ‖y' s - y' t‖ := h_norm_le
    _ ≤ ∫ s in t..(t + k), M * (s - t)     := h_mono
    _ = (k^2 / 2) * M                      := h_eval_integral


section Scalar

/-! ## Scalar Euler bounds -/

variable {f : ℝ → ℝ → ℝ} {x0 : ℚ} {t₀ T : ℚ}

/-- Bound the global Euler error by accumulating local truncation and model errors.

At every grid point `tₙ` of `[t₀, T]`,

`|y tₙ - xₙ| ≤ (tₙ - t₀) · (ε + M δ / 2) · exp (K (tₙ - t₀))`.

This is the textbook form of the bound. It is convenient to state but lossy; for the
sharp, exactly rational version use `ODE.euler_bound_solution_rational`. -/
theorem euler_bound_solution (y : ℝ → ℝ) (K : NNReal) (M : ℚ) (hMne : M > 0)
      (hT : t₀ < T)
      (hx : SolutionExists f (x0 : ℝ) y (t₀ : ℝ) (T : ℝ)
              (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo (t₀ : ℝ) (T: ℝ), |iteratedDeriv 2 y t| ≤ (M : ℝ))
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
                  · specialize hK (S.t i) (by grind)
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

/-- One step of the Euler error recurrence.

`|y tₙ₊₁ - xₙ₊₁| ≤ |y tₙ - xₙ| · (1 + K δ) + (ε + M δ / 2) · δ`.

The `(1 + K δ)` factor is the amplification of the error already present, coming from
the Lipschitz hypothesis; the additive term is the new error committed by this step,
namely `M δ² / 2` of Taylor truncation (`ODE.taylor_lagrange_norm_bound_two`) plus
`ε δ` of model mismatch. Every global bound in this file is obtained by solving this
recurrence. -/
theorem euler_bound_solution_iterate {ε : ℚ} (y : ℝ → ℝ) (K : NNReal) (M : ℚ)
      (hT : t₀ < T)
      (hx : SolutionExists f (x0 : ℝ) y (t₀ : ℝ) (T : ℝ)
              (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo (t₀ : ℝ) (T: ℝ), |iteratedDeriv 2 y t| ≤ (M : ℝ))
      (S : Scheme) (hS : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0) :
      ∀ n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊),
       |y (S.t (n + 1)) - S.x (n+1)| ≤ |y (S.t (n)) - S.x (n)|
        * (1 + K * S.δ) + (ε + M * S.δ/2) * S.δ := by
      set N : ℕ := ⌊(T - S.t₀) / S.δ⌋₊ with hNdef
      have hε : (0 : ℝ) ≤ ε := le_trans (b := |f 0 0 - m 0 0|) (by grind) (by exact_mod_cast hf 0 0)
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
      have hnN : n < N := by grind
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
                  · specialize hK (S.t i) (by grind)
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
      exact hmain n hn

/-- The sharp, exactly rational global error bound at every grid point:

`|y tₙ - xₙ| ≤ (ε + M δ / 2) · δ · ((1 + K δ)ⁿ - 1) / (K δ)`.

Obtained by closing the recurrence of `ODE.euler_bound_solution_iterate` with discrete
Grönwall (`discrete_gronwall_prod_general`) and summing the resulting geometric series,
rather than by overestimating it with an exponential as `ODE.euler_bound_solution`
does.

Every constant on the right is rational, so the bound is a number a machine can
produce and check exactly; this is the form consumed by `DynaLean.Refinement`,
`DynaLean.RulesBound` and `DynaLean.DigitalTwin` (where it appears as `ODE.EB`). -/
theorem euler_bound_solution_rational {y} {ε K : ℚ} (M : ℚ) (hMne : M > 0)
      (hKne : K > (0 : ℝ))
      (hx : SolutionExists f (x0 : ℝ) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (S : Scheme) (hT : t₀ < T)
      (hf : ∀ t x : ℚ, |f t x - S.m t x| ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ), |iteratedDeriv 2 y t| ≤ (M : ℝ))
      (hS : S.t₀ = t₀ ∧ S.x₀ = x0)
      : ∀ n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1),
          |y ↑(S.t n) - ↑(S.x n)| ≤
          ((↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ) := by
            have heuler := euler_bound_solution_iterate
              y (K : ℝ).toNNReal M hT hx hcont S.m hf hK hM S (And.intro rfl hS)
            have heps : (0 : ℝ) ≤ (ε : ℝ) := le_trans (b := |f 0 0 - S.m 0 0|) (by grind)
                                              (by exact_mod_cast hf 0 0)
            have hδ := S.hδ
            intro n hn
            have hu : (∀ n ≥ 0,
    (if n + 1 ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
    then |y ↑(S.t (n + 1)) - ↑(S.x (n + 1))| else 0) ≤
      ((1 + ↑K * ↑S.δ) * if n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
      then |y ↑(S.t n) - ↑(S.x n)| else 0) +
        (↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) := by
              intro n hn
              by_cases h : n + 1 ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
              · simp only [ite_eq_left h]
                have g : n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1) := by
                  have hlt : n + 1 ≤ ⌊(T - S.t₀) / S.δ⌋₊ + 1 := by grind
                  have hlt' : n < ⌊(T - S.t₀) / S.δ⌋₊ + 1 := Nat.lt_of_succ_le hlt
                  exact Finset.mem_range.mpr hlt'
                simp only [ite_eq_left g]
                specialize heuler n (by grind)
                have triv : ((K : ℝ).toNNReal : ℝ) = (K : ℝ) := by
                  simp only [Real.toNNReal]; simp only [NNReal.coe_mk,
                  sup_eq_left, Rat.cast_nonneg]; exact_mod_cast hKne.le
                grind
              · simp only [ite_eq_right h]
                have triv : 0 < K := by exact_mod_cast hKne
                positivity
            have triv : 0 < K := by exact_mod_cast hKne
            have fin := discrete_gronwall_prod_general (n₀ := 0) (n := n)
             (u := fun n => if n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
             then |y ↑(S.t n) - ↑(S.x n)| else 0)
             (b := fun n => (ε + M * S.δ/2) * S.δ) (c := fun n => 1 + K * S.δ) hu
             (by intro n hn; positivity) (by grind)
            rw [hS.1, ite_eq_left hn] at fin
            rw [ite_eq_left] at fin
            · simp only [Scheme.t, Scheme.x] at fin
              simp only [hS.1, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, CharP.cast_eq_zero,
              zero_mul, add_zero, hS.2,
      Nat.Ico_zero_eq_range, Finset.prod_const, Finset.card_range, Nat.card_Ico, hx.1] at fin
              simp only [sub_self, abs_zero, zero_mul, zero_add] at fin
              rw [← Finset.mul_sum] at fin
              rw [Finset.sum_congr rfl
              (by intro i hi; rw [show n - (i + 1) = n - 1 - i by omega])] at fin
              have : (K : ℝ) * S.δ > 0 := by positivity
              rw [Finset.sum_range_reflect, geom_sum_eq (by grind)] at fin
              simp only [add_sub_cancel_left] at fin
              simp only [Scheme.t, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, ge_iff_le]
              grind
            · grind


/-- Construct an Euler scheme whose final grid point is `T`.

Takes `N` equal steps of size `δ = (T - t₀) / N`, so that `t N = T` exactly and
`⌊(T - t₀)/δ⌋ = N`. Without this alignment the last grid point would in general fall
short of `T` and the bounds could say nothing about the right endpoint. -/
def LastSchema (t₀ T : ℚ) (x0 : ℚ) (m : ℚ → ℚ → ℚ) (N : ℕ) (hN : N ≠ 0) (ht : t₀ < T) : Scheme where
  δ := (T - t₀) / N
  hδ := by positivity
  t₀ := t₀
  x₀ := x0
  m := m


/-- Specialize the Euler error bound to a scheme ending exactly at `T`.

For `S = ODE.LastSchema t₀ T x₀ m N`, the interpolant at the right endpoint satisfies
`|y T - S.pl T| ≤ (T - t₀) · (ε + M δ / 2) · exp (K (T - t₀))`. This is
`ODE.euler_bound_solution` evaluated at `n = N`, using `S.t N = T`. -/
theorem euler_bound_solution_last (y : ℝ → ℝ) (K : NNReal) (M : ℚ) (hMne : M > 0)
      (hx : SolutionExists f (x0 : ℝ) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : NNReal) (fun x => f t x))
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

/-- Extend a grid-point error bound to every time *inside* a cell.

For `s` anywhere in `[tᵢ, tᵢ + δ]`, the distance from `y s` to the affine piece
`xᵢ + (s - tᵢ) · m tᵢ xᵢ` obeys the same right-hand side as the one-step recurrence
`ODE.euler_bound_solution_iterate`, namely
`|y tᵢ - xᵢ| · (1 + K δ) + (ε + M δ / 2) · δ`.

Taking `s = tᵢ₊₁` recovers that recurrence; the point of the lemma is the intermediate
`s`, which is what upgrades a statement about grid points into a statement about the
whole interpolant (`ODE.euler_bound_solution_all`). -/
theorem euler_bound_cell {ε : ℚ} (y : ℝ → ℝ) (K : NNReal) (M : ℚ) (hM0 : 0 ≤ M)
      (hT : t₀ < T)
      (hx : SolutionExists f (x0 : ℝ) y (t₀ : ℝ) (T : ℝ) (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo (t₀ : ℝ) (T : ℝ), |iteratedDeriv 2 y t| ≤ (M : ℝ))
      (S : Scheme) (hS : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0) :
      ∀ i ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊),
      ∀ s ∈ Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)),
       |y s - ((S.x i : ℝ) + (s - ((S.t i : ℚ) : ℝ)) * ((S.m (S.t i) (S.x i) : ℚ) : ℝ))|
        ≤ |y (S.t i) - S.x i| * (1 + K * S.δ) + (ε + M * S.δ/2) * S.δ := by
  set N : ℕ := ⌊(T - S.t₀) / S.δ⌋₊ with hNdef
  have hε : (0 : ℝ) ≤ ε :=
    le_trans (b := |f 0 0 - m 0 0|) (by grind) (by exact_mod_cast hf 0 0)
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
  intro i hi s hs
  have hiN : i < N := Finset.mem_range.mp hi
  ---------------------------------------------------------------- preamble, verbatim
  have hne : (S.δ : ℝ) ≠ 0 := by rw [Rat.cast_ne_zero]; exact S.hδ.ne'
  have hδR : (0 : ℝ) < ((S.δ : ℚ) : ℝ) := by exact_mod_cast S.hδ
  have hab : ((S.t i : ℚ) : ℝ) < ((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) := by linarith
  have hstep : (S.t i : ℚ) + S.δ = S.t (i + 1) := by rw [htQ, htQ]; push_cast; ring
  have hti : ((t₀ : ℚ) : ℝ) ≤ ((S.t i : ℚ) : ℝ) := by exact_mod_cast hge i
  have htiT : ((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) ≤ ((T : ℚ) : ℝ) := by
    have h := hle (i + 1) (by omega)
    rw [← hstep] at h
    exact_mod_cast h
  have hIcc : Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))
      ⊆ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := Set.Icc_subset_Icc hti htiT
  have hd1 : ContDiffOn ℝ 1
      (derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))))
      (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) :=
    (hcont.mono hIcc).derivWithin (uniqueDiffOn_Icc hab) (by decide)
  set y'' := fun u => derivWithin
      (derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))))
      (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) u with hy''def
  have hM' : ∀ u ∈ Set.Ioo ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)),
      ‖y'' u‖ ≤ (M : ℝ) := by
    intro u hu
    have hmem : u ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := by grind
    specialize hM u hmem
    have hseteq : y'' u = iteratedDeriv 2 y u := by
      simp only [y'']
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
      have h_ev : derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ)
          (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) =ᶠ[𝓝 u] deriv y := by
        filter_upwards [(isOpen_Ioo.mem_nhds hu)] with v hv
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hv.1 hv.2)
      rw [h_ev.deriv_eq]
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hseteq, Real.norm_eq_abs]
    exact hM
  have hderivI : derivWithin y
      (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) ((S.t i : ℚ) : ℝ)
      = f (S.t i) (y (S.t i)) := by
    have hmem : ((S.t i : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := ⟨hti, by linarith⟩
    exact ((hx.2 _ hmem).mono hIcc).derivWithin
      (uniqueDiffOn_Icc hab _ (Set.left_mem_Icc.mpr hab.le))
  set θ : ℝ := s - ((S.t i : ℚ) : ℝ) with hθdef
  have hθ0 : 0 ≤ θ := by simp only [hθdef]; linarith [hs.1]
  have hθδ : θ ≤ ((S.δ : ℚ) : ℝ) := by simp only [hθdef]; linarith [hs.2]
  have hsEq : ((S.t i : ℚ) : ℝ) + θ = s := by simp only [hθdef]; ring
  have hsubI : Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + θ)
      ⊆ Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)) :=
    Set.Icc_subset_Icc le_rfl (by linarith)
  have hcp := taylor_lagrange_norm_bound_two (E := ℝ) (M := (M : ℝ)) (y := y) (y'' := y'')
      (t := ((S.t i : ℚ) : ℝ)) (k := θ) (hk := hθ0)
      (hy := fun u hu =>
        ((((hcont.mono hIcc) u (hsubI hu)).differentiableWithinAt
            (by decide)).hasDerivWithinAt).mono hsubI)
      (hy_cont := hd1.continuousOn.mono hsubI)
      (hy' := fun u hu => by
        dsimp [y'']
        exact ((((hd1 u (hsubI hu)).differentiableWithinAt
            (by decide)).hasDerivWithinAt)).mono hsubI)
      (hM := fun u hu => hM' u ⟨hu.1, lt_of_lt_of_le hu.2 (by linarith)⟩)
  rw [hsEq, hderivI, Real.norm_eq_abs, smul_eq_mul] at hcp
  have hsplit : y s - ((S.x i : ℝ) + θ * ((S.m (S.t i) (S.x i) : ℚ) : ℝ))
      = (y s - y (S.t i) - θ * f (S.t i) (y (S.t i)))
        + (y (S.t i) - (S.x i : ℝ))
        + θ * (f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ) : ℝ)) := by ring
  have hfm : |f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ) : ℝ)|
      ≤ (K : ℝ) * |y (S.t i) - (S.x i : ℝ)| + ε := by
    have hmodel : |f (S.t i) ((S.x i : ℚ) : ℝ) - ((S.m (S.t i) (S.x i) : ℚ) : ℝ)| ≤ (ε : ℝ) := by
      rw [hS.1]; exact_mod_cast hf (S.t i) (S.x i)
    have hlip : |f (S.t i) (y (S.t i)) - f (S.t i) ((S.x i : ℚ) : ℝ)|
        ≤ (K : ℝ) * |y (S.t i) - (S.x i : ℝ)| := by
      have hmem : ((S.t i : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := ⟨hti, by linarith⟩
      have h := (hK (S.t i) hmem).dist_le_mul (y (S.t i)) ((S.x i : ℚ) : ℝ)
      rwa [Real.dist_eq, Real.dist_eq] at h
    calc |f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ) : ℝ)|
        ≤ |f (S.t i) (y (S.t i)) - f (S.t i) ((S.x i : ℚ) : ℝ)|
          + |f (S.t i) ((S.x i : ℚ) : ℝ) - ((S.m (S.t i) (S.x i) : ℚ) : ℝ)| := by
          have := abs_add_le (f (S.t i) (y (S.t i)) - f (S.t i) ((S.x i : ℚ) : ℝ))
                          (f (S.t i) ((S.x i : ℚ) : ℝ) - ((S.m (S.t i) (S.x i) : ℚ) : ℝ))
          simpa using this
      _ ≤ _ := by linarith
  have hC : |θ * (f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ) : ℝ))|
      ≤ θ * ((K : ℝ) * |y (S.t i) - (S.x i : ℝ)| + ε) := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact mul_le_mul_of_nonneg_left hfm hθ0
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
  have hθsq : θ ^ 2 ≤ ((S.δ : ℚ) : ℝ) ^ 2 := by nlinarith [hθ0, hθδ]
  have hA : |y s - y (S.t i) - θ * f (S.t i) (y (S.t i))|
      ≤ ((S.δ : ℚ) : ℝ) ^ 2 / 2 * (M : ℝ) :=
    hcp.trans (mul_le_mul_of_nonneg_right (by linarith) hMR)
  have hKBε : (0 : ℝ) ≤ (K : ℝ) * |y (S.t i) - (S.x i : ℝ)| + (ε : ℝ) :=
    add_nonneg (mul_nonneg K.coe_nonneg (abs_nonneg _)) hε
  have hC2 := hC.trans (mul_le_mul_of_nonneg_right hθδ hKBε)
  rw [hsplit]
  refine le_trans (abs_add_three _ _ _) ?_
  exact le_trans (add_le_add (add_le_add hA le_rfl) hC2) (le_of_eq (by ring))

/-- The global bound, at every time of `[t₀, T]` rather than only at grid points.

For `S = ODE.LastSchema t₀ T x₀ m N` and every `s ∈ [t₀, T]`,

`|y s - S.plRR s| ≤ (ε + M δ / 2) · δ · ((1 + K δ)ᴺ - 1) / (K δ)`,

where `S.plRR` is the piecewise-linear interpolant through the Euler iterates. Proved
by combining the grid-point bound `ODE.euler_bound_solution_rational` with the
intra-cell bound `ODE.euler_bound_cell`, and using that the right-hand side is
monotone in the step index so the value at `N` dominates every cell. -/
theorem euler_bound_solution_all {y : ℝ → ℝ} {ε K : ℚ} (M : ℚ) (hMne : M > 0)
      (hKne : K > (0 : ℝ))
      (hx : SolutionExists f (x0 : ℝ) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (m : ℚ → ℚ → ℚ)
      (hf : ∀ t x : ℚ, |f t x - m t x| ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ), |iteratedDeriv 2 y t| ≤ (M : ℝ))
      (N : ℕ) (hN : N ≠ 0) (ht : t₀ < T)
      (S : Scheme) (hS : S = LastSchema t₀ T x0 m N hN ht) :
      ∀ s ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ),
        |y s - S.plRR s|
          ≤ ((↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) * (((1 + K*S.δ) ^ N) - 1)/(K * S.δ) := by
  have hS' : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0 := by
    simp only [hS]; exact ⟨rfl, rfl, rfl⟩
  have hδeq : S.δ = (T - t₀) / N := by rw [hS]; rfl
  have hNQ : ((N : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdiv : (T - S.t₀) / S.δ = ((N : ℕ) : ℚ) := by rw [hS'.2.1, hδeq]; field_simp; grind
  have hfloor : ⌊(T - S.t₀) / S.δ⌋₊ = N := by rw [hdiv]; simp
  have htN : S.t N = T := by
    simp only [hS, Scheme.t_succ', LastSchema]; field_simp; ring
  have hKR : (0 : ℝ) < (K : ℝ) := hKne
  have hδR : (0 : ℝ) < ((S.δ : ℚ) : ℝ) := by exact_mod_cast S.hδ
  have hεR : (0 : ℝ) ≤ (ε : ℝ) :=
    le_trans (b := |f 0 0 - m 0 0|) (by grind) (by exact_mod_cast hf 0 0)
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMne.le
  set A : ℝ := ((ε : ℝ) + (M : ℝ) * ((S.δ : ℚ) : ℝ) / 2) * ((S.δ : ℚ) : ℝ) with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  set EBr : ℕ → ℝ := fun j => A * (((1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) ^ j) - 1)
                                / ((K : ℝ) * ((S.δ : ℚ) : ℝ)) with hEBrdef
  have hEBapp : ∀ j : ℕ, EBr j
      = A * (((1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) ^ j) - 1) / ((K : ℝ) * ((S.δ : ℚ) : ℝ)) := by
    intro j; simp only [hEBrdef]
  have hEBrec : ∀ j : ℕ, EBr j * (1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) + A = EBr (j + 1) := by
    intro j; simp only [hEBrdef]; field_simp; ring
  have hEBmono : Monotone EBr := by
    intro a b hab
    simp only [hEBrdef]
    gcongr
    simp only [le_add_iff_nonneg_right]
    positivity
  have hgrid := euler_bound_solution_rational (f := f) (x0 := x0) (t₀ := t₀) (T := T)
      M hMne hKne hx hcont S ht (by rw [hS'.1]; exact hf) hK hM hS'.2
  have hgrid' : ∀ j : ℕ, j ≤ N → |y (S.t j) - (S.x j : ℝ)| ≤ EBr j := by
    intro j hj
    have hmem : j ∈ Finset.range (⌊(T - t₀) / S.δ⌋₊ + 1) := by
      rw [← hS'.2.1, hfloor]; exact Finset.mem_range.mpr (by omega)
    simpa [hEBapp, hAdef, mul_comm, mul_assoc, mul_left_comm] using hgrid j hmem
  have hcell := euler_bound_cell (f := f) (x0 := x0) (t₀ := t₀) (T := T)
      y (K : ℝ).toNNReal M hMne.le ht hx hcont m hf hK hM S hS'
  intro s hs
  rw [← hEBapp N]
  set n : ℕ := S.idxR s with hndef
  set q : ℝ := (s - ((S.t₀ : ℚ) : ℝ)) / ((S.δ : ℚ) : ℝ) with hqdef
  have ht₀S : S.t₀ = t₀ := hS'.2.1
  have hq0 : 0 ≤ q := by rw [hqdef, ht₀S]; exact div_nonneg (by linarith [hs.1]) hδR.le
  have hqN : q ≤ (N : ℝ) := by
    rw [hqdef, ht₀S, div_le_iff₀ hδR]
    have : ((T : ℚ) : ℝ) = ((t₀ : ℚ) : ℝ) + (N : ℝ) * ((S.δ : ℚ) : ℝ) := by
      rw [← htN]; simp only [Scheme.t_succ', ht₀S]; push_cast; ring
    linarith [hs.2]
  have hfl0 : 0 ≤ ⌊q⌋ := Int.le_floor.mpr (by exact_mod_cast hq0)
  have hncast : (n : ℝ) = (⌊q⌋ : ℝ) := by
    rw [hndef, Scheme.idxR, ← hqdef]
    norm_cast
    simp only [Int.ofNat_toNat, sup_eq_left]
    exact hfl0
  have hnq : (n : ℝ) ≤ q := by rw [hncast]; exact Int.floor_le q
  have hqn : q < (n : ℝ) + 1 := by rw [hncast]; exact Int.lt_floor_add_one q
  have hnN : n ≤ N := by
    have : (n : ℝ) ≤ (N : ℝ) := le_trans hnq hqN
    exact_mod_cast this
  have hs' : s = ((S.t₀ : ℚ) : ℝ) + q * ((S.δ : ℚ) : ℝ) := by rw [hqdef]; field_simp; grind
  have htn_le : ((S.t n : ℚ) : ℝ) ≤ s := by
    rw [hs']; simp only [Scheme.t_succ']; push_cast; nlinarith [hnq, hδR]
  have hs_le : s ≤ ((S.t n : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) := by
    rw [hs']; simp only [Scheme.t_succ']; push_cast; nlinarith [hqn, hδR]
  have hplR : S.plRR s
      = (S.x n : ℝ) + (s - ((S.t n : ℚ) : ℝ)) * ((S.m (S.t n) (S.x n) : ℚ) : ℝ) := by
    simp only [Scheme.plRR, ← hndef]
  rcases lt_or_eq_of_le hnN with hlt | heq
  · rw [hplR]
    refine le_trans (hcell n (by rw [hfloor]; exact Finset.mem_range.mpr hlt) s
        ⟨htn_le, hs_le⟩) ?_
    have hKcast : (((K : ℝ).toNNReal : NNReal) : ℝ) = (K : ℝ) := by
      simp only [Real.toNNReal]
      simp only [NNReal.coe_mk, sup_eq_left, Rat.cast_nonneg]
      exact_mod_cast hKne.le
    rw [hKcast]
    calc |y (S.t n) - (S.x n : ℝ)| * (1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) + A
        ≤ EBr n * (1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) + A := by
          have h1 : (0 : ℝ) ≤ 1 + (K : ℝ) * ((S.δ : ℚ) : ℝ) := by positivity
          exact add_le_add_left
            (mul_le_mul_of_nonneg_right (hgrid' n hlt.le) h1) A
      _ = EBr (n + 1) := hEBrec n
      _ ≤ EBr N := hEBmono (by omega)
  · subst heq
    have hsT : s = ((S.t n : ℚ) : ℝ) :=
      le_antisymm (by rw [htN]; exact hs.2) htn_le
    rw [hplR, hsT]
    simp only [sub_self, zero_mul, add_zero]
    exact hgrid' n le_rfl


end Scalar


section Vector


open Set Filter Metric
open scoped Interval

open Set Filter Topology Interval

/-! ## Euler bounds for systems

The scalar development repeated for `ℝ^k`-valued solutions, with `|·|` replaced by the
Euclidean norm `‖·‖`. These are the versions used by `DynaLean.DigitalTwin`. -/

variable {k : ℕ} (f : ℝ → (ℝ^k) → ℝ^k) (x0 : ℚ^k) (t₀ T : ℚ)

/-- One step of the Euler error recurrence, for systems.

`‖y tₙ₊₁ - xₙ₊₁‖ ≤ ‖y tₙ - xₙ‖ · (1 + K δ) + (ε + M δ / 2) · δ`.

The `ℝ^k` analogue of `ODE.euler_bound_solution_iterate`. -/
theorem euler_bound_solution_iterate_vector {ε : ℚ} (y : ℝ → ℝ^k) (K : NNReal) (M : ℚ)
      (hT : t₀ < T)
      (hx : SolutionExistsVector f (x0 : ℝ^k) y (t₀ : ℝ) (T : ℝ)
              (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (m : ℚ → (ℚ^k) → ℚ^k)
      (hf : ∀ (t : ℚ) (x : ℚ^k), ‖f t x - m t x‖ ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo (t₀ : ℝ) (T : ℝ), ‖iteratedDeriv 2 y t‖ ≤ (M : ℝ))
      (S : VectorScheme k) (hS : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0) :
      ∀ n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊),
       ‖y (S.t (n + 1)) - S.x (n+1)‖ ≤ ‖y (S.t (n)) - S.x (n)‖
        * (1 + K * S.δ) + (ε + M * S.δ/2) * S.δ := by
      set N : ℕ := ⌊(T - S.t₀) / S.δ⌋₊ with hNdef
      have hε : (0 : ℝ) ≤ ε := le_trans (b := ‖f 0 0 - m 0 0‖) (by grind)
        (by specialize hf 0 0; simp only [Rat.cast_zero,
            PiLp.zero_apply, WithLp.equiv_symm_apply] at hf; simp only [WithLp.equiv_symm_apply];
            have : (WithLp.toLp 2 fun (i : Fin k) ↦ (0 : ℝ)) = 0 := rfl
            rw [this] at hf; exact hf)
      -- grid points, in ℚ
      have htQ : ∀ j : ℕ, S.t j = t₀ + (j : ℚ) * S.δ := by
        intro j; rw [VectorScheme.t_succ', hS.2.1]
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
      set e := fun n => ‖y (S.t n) - S.x n‖ with heq
      intro n hn
      have hnN : n < N := by grind
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
        set y'' := fun t => derivWithin (derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ)
        + ((S.δ : ℚ) : ℝ))))
          (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) t with hy''
        have hM' : ∀ s ∈ Set.Ioo ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)),
            ‖y'' s‖ ≤ (M : ℝ) := by
          intro s hs
          have hmem : s ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := by grind
          specialize hM s hmem
          have hseteq : y'' s = iteratedDeriv 2 y s := by
            dsimp [y'']
            rw [derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
            have h_ev : derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ)
              (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) =ᶠ[𝓝 s] deriv y := by
                filter_upwards [(isOpen_Ioo.mem_nhds hs)] with u hu
                exact derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)
            rw [h_ev.deriv_eq]
            -- 4. Connect deriv (deriv y) to iteratedDeriv 2 y
            rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
          rw [hseteq]
          exact hM
        have hcp :=
          taylor_lagrange_norm_bound_two (M := M) (y := y)
            (y'' := y'')
            (hk := by positivity)
            (hy := fun s hs =>
            (((hcont.mono hIcc) s hs).differentiableWithinAt (by decide)).hasDerivWithinAt)
            (hy_cont := hd1.continuousOn)
            (hy' := fun s hs => by dsimp [y'']; exact
            ((hd1 s hs).differentiableWithinAt (by decide)).hasDerivWithinAt)
            (hM := fun s hs => hM' s hs)
        -- the Euler direction really is `derivWithin y` at the left endpoint
        have hderiv : derivWithin y (Set.uIcc (S.t i) (S.t i + S.δ)) (S.t i)
            = f (S.t i) (y (S.t i)) := by
            have hmem : ((S.t i : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) :=
              ⟨hti, by linarith⟩
            rw [Set.uIcc_of_le hab.le]
            exact ((hx.2 _ hmem).mono hIcc).derivWithin
              (uniqueDiffOn_Icc hab _ (Set.left_mem_Icc.mpr hab.le))
        have step1 : ‖y (S.t (i + 1)) - S.x (i + 1)‖
            = ‖y (S.t i + S.δ) - S.x i - S.δ • m (S.t i) (S.x i)‖ := by
            simp only [VectorScheme.x_succ, VectorScheme.t_succ, hS.1]
            push_cast
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Rat.cast_add, Rat.cast_mul,
              WithLp.equiv_symm_apply]
            congr 1
            rw [sub_sub]
            congr 1
        have step2 : ‖y (S.t i + S.δ) - S.x i - S.δ • m (S.t i) (S.x i)‖
            = ‖y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i))
              + y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖ :=
              by
              push_cast
              congr
              grind
        have step3 :
          ‖y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i))
              + y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖
            ≤ ‖y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i))‖
              + ‖y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖ :=
        calc ‖y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i))
                + y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖
            = ‖(y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i)))
                + (y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i))‖ := by
              congr 1
              abel
          _ ≤ _ := norm_add_le _ _
        have step4_1 : ‖y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i))‖
            ≤ S.δ^2 / 2 * M := by
            have hset : [[(S.t i : ℝ), S.t i + S.δ]] = Set.Icc ((S.t i : ℝ)) (S.t i + S.δ) := by
              rw [Set.uIcc_of_le hab.le]
            rw [hset] at hderiv
            rw [hderiv] at hcp
            exact hcp
        have step4_2 : ‖y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖
            ≤ ‖y (S.t i) - S.x i‖ + ‖S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖ := by
            calc
              ‖y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖
                = ‖(y (S.t i) - S.x i) + (S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i))‖
                := by
                congr 1
                abel
              _ ≤ _ := norm_add_le _ _
        have step5 : ‖S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖
            ≤ S.δ * (ε + K * ‖y (S.t i) - S.x i‖) := by
            have hsplit : ‖S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖
                = ‖S.δ • (f (S.t i) (y (S.t i)) - m (S.t i) (S.x i))‖ := by
              congr 1
              rw [smul_sub]
            have hsplit' : ‖S.δ • (f (S.t i) (y (S.t i)) - m (S.t i) (S.x i))‖
                = S.δ * ‖f (S.t i) (y (S.t i)) - m (S.t i) (S.x i)‖ := by
              rw [norm_smul]
              rw [← Real.norm_of_nonneg (r := (S.δ : ℝ)) (by positivity)]
              norm_cast
            rw [hsplit, hsplit']
            apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast S.hδ.le)
            have hsplit'' : ‖f (S.t i) (y (S.t i)) - m (S.t i) (S.x i)‖
                ≤ ‖f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)‖
                  + ‖f (S.t i) (S.x i) - m (S.t i) (S.x i)‖ := by
              calc
                ‖f (S.t i) (y (S.t i)) - m (S.t i) (S.x i)‖
                  = ‖(f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)) +
                  (f (S.t i) (S.x i) - m (S.t i) (S.x i))‖ := by
                  congr 1
                  abel
                _ ≤ _ := norm_add_le _ _
            have hsplit''' : ‖f (S.t i) (S.x i) - m (S.t i) (S.x i)‖ ≤ ε := by
              specialize hf (S.t i) (S.x i)
              exact hf
            have hsplit'''' : ‖f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)‖
                ≤ K * ‖y (S.t i) - S.x i‖ := by
              have hmem : ((S.t i : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
                := ⟨hti, by linarith⟩
              specialize hK (S.t i) hmem (y (S.t i)) (S.x i)
              simp only [edist_dist] at hK
              simp only [ENNReal.ofReal, WithLp.equiv_symm_apply] at hK
              norm_cast at hK
              have h_real : dist (f (↑(S.t i)) (y ↑(S.t i)))
                  (f (↑(S.t i)) ((WithLp.equiv 2 (Fin k → ℝ)).symm fun i_1 ↦ ↑((S.x i).ofLp i_1))) ≤
                ↑K * dist (y ↑(S.t i))
                  ((WithLp.equiv 2 (Fin k → ℝ)).symm fun i_1 ↦ ↑((S.x i).ofLp i_1)) := by
                have h := NNReal.coe_le_coe.mpr hK
                rw [NNReal.coe_mul, Real.coe_toNNReal, Real.coe_toNNReal] at h
                · exact h
                · positivity
                · positivity
              rwa [dist_eq_norm, dist_eq_norm] at h_real
            calc
              ‖f (S.t i) (y (S.t i)) - m (S.t i) (S.x i)‖
                ≤ ‖f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)‖
                  + ‖f (S.t i) (S.x i) - m (S.t i) (S.x i)‖ := hsplit''
              _ ≤ K * ‖y (S.t i) - S.x i‖ + ε := by linarith [hsplit''', hsplit'''']
              _ = ε + K * ‖y (S.t i) - S.x i‖ := by ring
        calc
          ‖y (S.t (i + 1)) - S.x (i + 1)‖
            = ‖y (S.t i + S.δ) - S.x i - S.δ • m (S.t i) (S.x i)‖ := step1
          _ = ‖y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i))
              + y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖ := step2
          _ ≤ ‖y (S.t i + S.δ) - y (S.t i) - S.δ • f (S.t i) (y (S.t i))‖
              + ‖y (S.t i) - S.x i + S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖ := step3
          _ ≤ S.δ^2 / 2 * M
              + ‖y (S.t i) - S.x i‖ + ‖S.δ • f (S.t i) (y (S.t i)) - S.δ • m (S.t i) (S.x i)‖
              := by linarith [step4_1, step4_2]
          _ ≤ S.δ^2 / 2 * M
              + ‖y (S.t i) - S.x i‖ + S.δ * (ε + K * ‖y (S.t i) - S.x i‖) := by linarith [step5]
          _ = ‖y (S.t i) - S.x i‖ * ((1 : ℝ) + K * ↑(S.δ : ℚ))
              + ((ε : ℝ) + M * ↑(S.δ : ℚ)/2)* ↑(S.δ : ℚ)
              := by ring
      exact hmain n hn

/-- The sharp, exactly rational grid-point error bound, for systems:

`‖y tₙ - xₙ‖ ≤ (ε + M δ / 2) · δ · ((1 + K δ)ⁿ - 1) / (K δ)`.

The `ℝ^k` analogue of `ODE.euler_bound_solution_rational`, again proved by discrete
Grönwall. The right-hand side is exactly `ODE.EB K ε M δ n` as used by the digital-twin
machinery. -/
theorem euler_bound_solution_rational_vector {y} {ε K : ℚ} (M : ℚ) (hMne : M > 0)
      (hKne : K > (0 : ℝ))
      (hx : SolutionExistsVector f (x0 : ℝ^k) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (S : VectorScheme k) (hT : t₀ < T)
      (hf : ∀ (t : ℚ) (x : ℚ^k), ‖f t (x : ℝ^k) - S.m t x‖ ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ), ‖iteratedDeriv 2 y t‖ ≤ (M : ℝ))
      (hS : S.t₀ = t₀ ∧ S.x₀ = x0)
      : ∀ n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1),
          ‖y ↑(S.t n) - ↑(S.x n)‖ ≤
          ((↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ) := by
            have heuler := euler_bound_solution_iterate_vector f x0 t₀ T
              y (K : ℝ).toNNReal M hT hx hcont S.m hf hK hM S (And.intro rfl hS)
            have hε : (0 : ℝ) ≤ ε := le_trans (b := ‖f 0 0 - S.m 0 0‖) (by grind)
              (by specialize hf 0 0; simp only [Rat.cast_zero,
                  PiLp.zero_apply, WithLp.equiv_symm_apply] at hf; simp only
                  [WithLp.equiv_symm_apply];
                  have : (WithLp.toLp 2 fun (i : Fin k) ↦ (0 : ℝ)) = 0 := rfl
                  rw [this] at hf; exact hf)
            have hδ := S.hδ
            intro n hn
            have hu : (∀ n ≥ 0,
    (if n + 1 ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
    then ‖y ↑(S.t (n + 1)) - ↑(S.x (n + 1))‖ else 0) ≤
      ((1 + ↑K * ↑S.δ) * if n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
      then ‖y ↑(S.t n) - ↑(S.x n)‖ else 0) +
        (↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) := by
              intro n hn
              by_cases h : n + 1 ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
              · simp only [ite_eq_left h]
                have g : n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1) := by
                  have hlt : n + 1 ≤ ⌊(T - S.t₀) / S.δ⌋₊ + 1 := by grind
                  have hlt' : n < ⌊(T - S.t₀) / S.δ⌋₊ + 1 := Nat.lt_of_succ_le hlt
                  exact Finset.mem_range.mpr hlt'
                simp only [ite_eq_left g]
                specialize heuler n (by grind)
                have triv : ((K : ℝ).toNNReal : ℝ) = (K : ℝ) := by
                  simp only [Real.toNNReal]; simp only [NNReal.coe_mk,
                  sup_eq_left, Rat.cast_nonneg]; exact_mod_cast hKne.le
                grind
              · simp only [ite_eq_right h]
                have triv : 0 < K := by exact_mod_cast hKne
                positivity
            have triv : 0 < K := by exact_mod_cast hKne
            have fin := discrete_gronwall_prod_general (n₀ := 0) (n := n)
             (u := fun n => if n ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)
             then ‖y ↑(S.t n) - ↑(S.x n)‖  else 0)
             (b := fun n => (ε + M * S.δ/2) * S.δ) (c := fun n => 1 + K * S.δ) hu
             (by intro n hn; positivity) (by grind)
            rw [hS.1, ite_eq_left hn] at fin
            rw [ite_eq_left] at fin
            · simp only [VectorScheme.t, VectorScheme.x] at fin
              simp only [hS.1, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, CharP.cast_eq_zero,
              zero_mul, add_zero, hS.2,
      Nat.Ico_zero_eq_range, Finset.prod_const, Finset.card_range, Nat.card_Ico, hx.1] at fin
              simp only [sub_self, norm_zero, zero_mul, zero_add] at fin
              rw [← Finset.mul_sum] at fin
              rw [Finset.sum_congr rfl
              (by intro i hi; rw [show n - (i + 1) = n - 1 - i by omega])] at fin
              have : (K : ℝ) * S.δ > 0 := by positivity
              rw [Finset.sum_range_reflect, geom_sum_eq (by grind)] at fin
              simp only [add_sub_cancel_left] at fin
              simp only [VectorScheme.t, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, ge_iff_le]
              grind
            · grind



/-- Construct a vector Euler scheme whose final grid point is `T`.

The `ℚ^k` analogue of `ODE.LastSchema`: `N` equal steps of size `(T - t₀) / N`, so that
`t N = T` exactly. This is the scheme `DynaLean.DigitalTwin` runs on each segment of a
measurement `Schedule`. -/
def LastVectorSchema (t₀ T : ℚ) (x0 : ℚ^k) (m : ℚ → (ℚ^k) → ℚ^k)
  (N : ℕ) (hN : N ≠ 0) (ht : t₀ < T) :
  VectorScheme k where
  δ := (T - t₀) / N
  hδ := by positivity
  t₀ := t₀
  x₀ := x0
  m := m


/-- Specialize the vector Euler error bound to a scheme ending exactly at `T`.

For `S = ODE.LastVectorSchema t₀ T x₀ m N`,
`‖y T - S.pl T‖ ≤ (ε + M δ / 2) · δ · ((1 + K δ)ᴺ - 1) / (K δ)`. This is
`ODE.euler_bound_solution_rational_vector` at `n = N`, using `S.t N = T`. -/
theorem euler_bound_solution_last_vector {ε : ℚ} (K : ℚ) (M : ℚ) (hMne : M > 0) (hKne : K > (0 : ℝ))
      (hx : SolutionExistsVector f (x0 : ℝ^k) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (m : ℚ → (ℚ^k) → ℚ^k)
      (hf : ∀ (t : ℚ) (x : ℚ^k), ‖f t (x : ℝ^k) - m t x‖ ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ), ‖iteratedDeriv 2 y t‖ ≤ (M : ℝ))
      (N : ℕ) (hN : N ≠ 0) (ht : t₀ < T)
      (S : VectorScheme k) (hS : S = LastVectorSchema t₀ T x0 m N hN ht) :
      ‖y T - S.pl T‖ ≤ ((↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) * (((1 + K*S.δ) ^ N) - 1)/(K * S.δ) := by
      have hS' : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0 := by
        simp only [hS]
        constructor
        · rfl
        · constructor <;> rfl
      have h := euler_bound_solution_rational_vector f x0 t₀ T M hMne
                  (by exact_mod_cast hKne) hx hcont S ht (by rw [hS'.1]; exact hf) hK hM hS'.2
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
            simp only [VectorScheme.t_succ']
            simp only [LastVectorSchema]
            field_simp
            ring
      calc
        _ = ‖y (S.t N) - S.pl (S.t N)‖ := by
          rw [htn]
        _ = ‖y (S.t N) - S.x N‖ := by
          simp only [VectorScheme.pl]
          rw [S.idx_eq_of_mem_Ico (k := k) (n := N) (s := S.t N) (by grind) (by simp only
          [S.t_succ', Nat.cast_add, Nat.cast_one, add_lt_add_iff_left, S.hδ, mul_lt_mul_iff_left₀,
            lt_add_iff_pos_right, zero_lt_one])]
          simp [VectorScheme.lOn]
        _ ≤ ((↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) * (((1 + K*S.δ) ^ N) - 1)/(K * S.δ) := by
          rw [hS'.2.1] at hmemN
          specialize h N hmemN
          rw [htn] at h
          have ht₀ : S.t₀ = t₀ := by simp only [hS]; rfl
          rwa [htn]

/-- Extend a grid-point error bound to every time inside a cell, for systems.

The `ℝ^k` analogue of `ODE.euler_bound_cell`: for `s ∈ [tᵢ, tᵢ + δ]` the distance from
`y s` to the affine piece `xᵢ + (s - tᵢ) • m tᵢ xᵢ` is at most
`‖y tᵢ - xᵢ‖ · (1 + K δ) + (ε + M δ / 2) · δ`. -/
theorem euler_bound_cell_vector {ε : ℚ} (y : ℝ → ℝ^k) (K : NNReal) (M : ℚ) (hM0 : 0 ≤ M)
      (hT : t₀ < T)
      (hx : SolutionExistsVector f (x0 : ℝ^k) y (t₀ : ℝ) (T : ℝ) (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) (T : ℝ)))
      (m : ℚ → (ℚ^k) → ℚ^k)
      (hf : ∀ (t : ℚ) (x : ℚ^k), ‖f t x - m t x‖ ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : NNReal) (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo (t₀ : ℝ) (T : ℝ), ‖iteratedDeriv 2 y t‖ ≤ (M : ℝ))
      (S : VectorScheme k) (hS : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0) :
      ∀ i ∈ Finset.range (⌊(T - S.t₀) / S.δ⌋₊),
      ∀ s ∈ Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)),
       ‖y s - ((S.x i : ℝ^k) + (s - ((S.t i : ℚ) : ℝ)) • ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k))‖
        ≤ ‖y (S.t i) - S.x i‖ * (1 + K * S.δ) + (ε + M * S.δ/2) * S.δ := by
  set N : ℕ := ⌊(T - S.t₀) / S.δ⌋₊ with hNdef
  have hε : (0 : ℝ) ≤ ε := le_trans (b := ‖f 0 0 - m 0 0‖) (by grind)
    (by specialize hf 0 0; simp only [Rat.cast_zero,
        PiLp.zero_apply, WithLp.equiv_symm_apply] at hf; simp only [WithLp.equiv_symm_apply]
        have : (WithLp.toLp 2 fun (i : Fin k) ↦ (0 : ℝ)) = 0 := rfl
        rw [this] at hf; exact hf)
  have htQ : ∀ j : ℕ, S.t j = t₀ + (j : ℚ) * S.δ := by
    intro j; rw [VectorScheme.t_succ', hS.2.1]
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
  intro i hi s hs
  have hiN : i < N := Finset.mem_range.mp hi
  have hne : (S.δ : ℝ) ≠ 0 := by rw [Rat.cast_ne_zero]; exact S.hδ.ne'
  have hδR : (0 : ℝ) < ((S.δ : ℚ) : ℝ) := by exact_mod_cast S.hδ
  have hab : ((S.t i : ℚ) : ℝ) < ((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) := by linarith
  have hstep : (S.t i : ℚ) + S.δ = S.t (i + 1) := by rw [htQ, htQ]; push_cast; ring
  have hti : ((t₀ : ℚ) : ℝ) ≤ ((S.t i : ℚ) : ℝ) := by exact_mod_cast hge i
  have htiT : ((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) ≤ ((T : ℚ) : ℝ) := by
    have h := hle (i + 1) (by omega)
    rw [← hstep] at h
    exact_mod_cast h
  have hIcc : Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))
      ⊆ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := Set.Icc_subset_Icc hti htiT
  have hd1 : ContDiffOn ℝ 1
      (derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))))
      (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) :=
    (hcont.mono hIcc).derivWithin (uniqueDiffOn_Icc hab) (by decide)
  set y'' := fun u => derivWithin
      (derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))))
      (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) u with hy''def
  have hM' : ∀ u ∈ Set.Ioo ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)),
      ‖y'' u‖ ≤ (M : ℝ) := by
    intro u hu
    have hmem : u ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := by grind
    specialize hM u hmem
    have hseteq : y'' u = iteratedDeriv 2 y u := by
      dsimp [y'']
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
      have h_ev : derivWithin y (Set.Icc ((S.t i : ℚ) : ℝ)
          (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) =ᶠ[𝓝 u] deriv y := by
        filter_upwards [(isOpen_Ioo.mem_nhds hu)] with v hv
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hv.1 hv.2)
      rw [h_ev.deriv_eq]
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hseteq]; exact hM
  have hderivI : derivWithin y
      (Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ))) ((S.t i : ℚ) : ℝ)
      = f (S.t i) (y (S.t i)) := by
    have hmem : ((S.t i : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := ⟨hti, by linarith⟩
    exact ((hx.2 _ hmem).mono hIcc).derivWithin
      (uniqueDiffOn_Icc hab _ (Set.left_mem_Icc.mpr hab.le))
  set θ : ℝ := s - ((S.t i : ℚ) : ℝ) with hθdef
  have hθ0 : 0 ≤ θ := by simp only [hθdef]; linarith [hs.1]
  have hθδ : θ ≤ ((S.δ : ℚ) : ℝ) := by simp only [hθdef]; linarith [hs.2]
  have hsEq : ((S.t i : ℚ) : ℝ) + θ = s := by simp only [hθdef]; ring
  have hsubI : Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + θ)
      ⊆ Set.Icc ((S.t i : ℚ) : ℝ) (((S.t i : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ)) :=
    Set.Icc_subset_Icc le_rfl (by linarith)
  have hcp := taylor_lagrange_norm_bound_two (M := (M : ℝ)) (y := y) (y'' := y'')
      (t := ((S.t i : ℚ) : ℝ)) (k := θ) (hk := hθ0)
      (hy := fun u hu =>
        ((((hcont.mono hIcc) u (hsubI hu)).differentiableWithinAt
            (by decide)).hasDerivWithinAt).mono hsubI)
      (hy_cont := hd1.continuousOn.mono hsubI)
      (hy' := fun u hu => by
        dsimp [y'']
        exact ((((hd1 u (hsubI hu)).differentiableWithinAt
            (by decide)).hasDerivWithinAt)).mono hsubI)
      (hM := fun u hu => hM' u ⟨hu.1, lt_of_lt_of_le hu.2 (by linarith)⟩)
  rw [hsEq, hderivI] at hcp
  have hsplit : y s - ((S.x i : ℝ^k) + θ • ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k))
      = (y s - y (S.t i) - θ • f (S.t i) (y (S.t i)))
        + (y (S.t i) - (S.x i : ℝ^k))
        + θ • (f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k)) := by
    rw [smul_sub]; abel
  have tri : ∀ a b c : ℝ^k, ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    intro a b c
    exact (norm_add_le (a + b) c).trans (add_le_add_left (norm_add_le a b) ‖c‖)
  -- the Lipschitz / model-error factor
  have hfm : ‖f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k)‖
      ≤ (K : ℝ) * ‖y (S.t i) - (S.x i : ℝ^k)‖ + ε := by
    have hsplit'' : ‖f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k)‖
        ≤ ‖f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)‖
          + ‖f (S.t i) (S.x i) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k)‖ := by
      calc ‖f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k)‖
          = ‖(f (S.t i) (y (S.t i)) - f (S.t i) (S.x i))
              + (f (S.t i) (S.x i) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k))‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hmodel : ‖f (S.t i) (S.x i) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k)‖ ≤ ε := by
      rw [hS.1]; exact hf (S.t i) (S.x i)
    have hlip : ‖f (S.t i) (y (S.t i)) - f (S.t i) (S.x i)‖
        ≤ (K : ℝ) * ‖y (S.t i) - (S.x i : ℝ^k)‖ := by
      have hmem : ((S.t i : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := ⟨hti, by linarith⟩
      have h := (hK (S.t i) hmem).dist_le_mul (y (S.t i)) ((S.x i : ℚ^k) : ℝ^k)
      rwa [dist_eq_norm, dist_eq_norm] at h
    linarith
  have hC : ‖θ • (f (S.t i) (y (S.t i)) - ((S.m (S.t i) (S.x i) : ℚ^k) : ℝ^k))‖
      ≤ θ * ((K : ℝ) * ‖y (S.t i) - (S.x i : ℝ^k)‖ + ε) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
    exact mul_le_mul_of_nonneg_left hfm hθ0
  have hBnn : (0 : ℝ) ≤ ‖y (S.t i) - (S.x i : ℝ^k)‖ := norm_nonneg _
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
  have hθsq : θ ^ 2 ≤ ((S.δ : ℚ) : ℝ) ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_nonneg hθ0, abs_of_nonneg (by exact_mod_cast S.hδ.le)]
    grind
  rw [hsplit]
  refine (tri _ _ _).trans ?_
  have hA : ‖y s - y (S.t i) - θ • f (S.t i) (y (S.t i))‖
      ≤ ((S.δ : ℚ) : ℝ) ^ 2 / 2 * (M : ℝ) := by
    refine hcp.trans ?_
    have : θ ^ 2 / 2 ≤ ((S.δ : ℚ) : ℝ) ^ 2 / 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hMR
  have hKBε : (0 : ℝ) ≤ (K : ℝ) * ‖y (S.t i) - ((S.x i : ℚ^k) : ℝ^k)‖ + (ε : ℝ) :=
  add_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg _)) hε
  have hC2 := hC.trans (mul_le_mul_of_nonneg_right hθδ hKBε)
  exact le_trans (add_le_add (add_le_add hA le_rfl) hC2) (le_of_eq (by ring))

/-- The global bound at every time of `[t₀, T]`, for systems.

For `S = ODE.LastVectorSchema t₀ T x₀ m N` and every `s ∈ [t₀, T]`,

`‖y s - S.plR s‖ ≤ (ε + M δ / 2) · δ · ((1 + K δ)ᴺ - 1) / (K δ)`.

The `ℝ^k` analogue of `ODE.euler_bound_solution_all`, and the result that
`DynaLean.DigitalTwin` discharges when it builds a `ODE.SegmentCert` for a segment. -/
theorem euler_bound_solution_all_vector {ε : ℚ} (K : ℚ) (M : ℚ) (hMne : M > 0)
      (hKne : K > (0 : ℝ))
      (hx : SolutionExistsVector f (x0 : ℝ^k) y ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)
              (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (hcont : ContDiffOn ℝ 2 y (Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ)))
      (m : ℚ → (ℚ^k) → ℚ^k)
      (hf : ∀ (t : ℚ) (x : ℚ^k), ‖f t (x : ℝ^k) - m t x‖ ≤ ε)
      (hK : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
      (hM : ∀ t ∈ Set.Ioo ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ), ‖iteratedDeriv 2 y t‖ ≤ (M : ℝ))
      (N : ℕ) (hN : N ≠ 0) (ht : t₀ < T)
      (S : VectorScheme k) (hS : S = LastVectorSchema t₀ T x0 m N hN ht) :
      ∀ s ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ),
        ‖y s - S.plR s‖
          ≤ ((↑ε + ↑M * ↑S.δ / 2) * ↑S.δ) * (((1 + K*S.δ) ^ N) - 1)/(K * S.δ) := by
  have hS' : S.m = m ∧ S.t₀ = t₀ ∧ S.x₀ = x0 := by
    simp only [hS]; exact ⟨rfl, rfl, rfl⟩
  have hδeq : S.δ = (T - t₀) / N := by rw [hS]; rfl
  have hNQ : ((N : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdiv : (T - S.t₀) / S.δ = ((N : ℕ) : ℚ) := by rw [hS'.2.1, hδeq]; field_simp; grind
  have hfloor : ⌊(T - S.t₀) / S.δ⌋₊ = N := by rw [hdiv]; simp
  have htN : S.t N = T := by
    simp only [hS, VectorScheme.t_succ', LastVectorSchema]; field_simp; ring
  have hKR : (0 : ℝ) < (K : ℝ) := hKne
  have hδR : (0 : ℝ) < ((S.δ : ℚ) : ℝ) := by exact_mod_cast S.hδ
  have hKδ : (0 : ℝ) < (K : ℝ) * ((S.δ : ℚ) : ℝ) := by positivity
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := le_trans (b := ‖f 0 0 - m 0 0‖) (by grind)
    (by specialize hf 0 0; simp only [Rat.cast_zero,
        PiLp.zero_apply, WithLp.equiv_symm_apply] at hf; simp only [WithLp.equiv_symm_apply]
        have : (WithLp.toLp 2 fun (i : Fin k) ↦ (0 : ℝ)) = 0 := rfl
        rw [this] at hf; exact hf)
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMne.le
  set A : ℝ := ((ε : ℝ) + (M : ℝ) * ((S.δ : ℚ) : ℝ) / 2) * ((S.δ : ℚ) : ℝ) with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  set EBr : ℕ → ℝ := fun j => A * (((1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) ^ j) - 1)
                                / ((K : ℝ) * ((S.δ : ℚ) : ℝ)) with hEBrdef
  have hEBrec : ∀ j : ℕ, EBr j * (1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) + A = EBr (j + 1) := by
    intro j; simp only [hEBrdef]; field_simp; ring
  have hEBmono : Monotone EBr := by
    intro a b hab
    simp only [hEBrdef]
    gcongr
    simp only [le_add_iff_nonneg_right]
    positivity
  have hgrid := euler_bound_solution_rational_vector f x0 t₀ T M hMne
      (by exact_mod_cast hKne) hx hcont S ht (by rw [hS'.1]; exact hf) hK hM hS'.2
  have hgrid' : ∀ j : ℕ, j ≤ N → ‖y (S.t j) - (S.x j : ℝ^k)‖ ≤ EBr j := by
    intro j hj
    have hmem : j ∈ Finset.range (⌊(T - t₀) / S.δ⌋₊ + 1) := by
      rw [← hS'.2.1, hfloor]; exact Finset.mem_range.mpr (by omega)
    simpa [hEBrdef, hAdef, mul_comm, mul_assoc, mul_left_comm] using hgrid j hmem
  have hcell := euler_bound_cell_vector f x0 t₀ T y (K : ℝ).toNNReal M hMne.le ht hx hcont m
      hf hK hM S hS'
  intro s hs
  have hEBapp : ∀ j : ℕ, EBr j
    = A * (((1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) ^ j) - 1) / ((K : ℝ) * ((S.δ : ℚ) : ℝ)) := by
    intro j; simp only [hEBrdef]
  rw [← hEBapp N]
  set n : ℕ := S.idxR s with hndef
  set q : ℝ := (s - ((S.t₀ : ℚ) : ℝ)) / ((S.δ : ℚ) : ℝ) with hqdef
  have ht₀S : S.t₀ = t₀ := hS'.2.1
  have hq0 : 0 ≤ q := by
    rw [hqdef, ht₀S]; exact div_nonneg (by linarith [hs.1]) hδR.le
  have hqN : q ≤ (N : ℝ) := by
    rw [hqdef, ht₀S, div_le_iff₀ hδR]
    have : ((T : ℚ) : ℝ) = ((t₀ : ℚ) : ℝ) + (N : ℝ) * ((S.δ : ℚ) : ℝ) := by
      rw [← htN]; simp only [VectorScheme.t_succ', ht₀S]; push_cast; ring
    linarith [hs.2]
  have hfl0 : 0 ≤ ⌊q⌋ := Int.le_floor.mpr (by exact_mod_cast hq0)
  have hncast : (n : ℝ) = (⌊q⌋ : ℝ) := by
    rw [hndef, VectorScheme.idxR, ← hqdef]
    norm_cast
    simp only [Int.ofNat_toNat, sup_eq_left]
    exact hfl0
  have hnq : (n : ℝ) ≤ q := by rw [hncast]; exact Int.floor_le q
  have hqn : q < (n : ℝ) + 1 := by rw [hncast]; exact Int.lt_floor_add_one q
  have hnN : n ≤ N := by
    have : (n : ℝ) ≤ (N : ℝ) := le_trans hnq hqN
    exact_mod_cast this
  have htn_le : ((S.t n : ℚ) : ℝ) ≤ s := by
    have hs' : s = ((S.t₀ : ℚ) : ℝ) + q * ((S.δ : ℚ) : ℝ) := by
      rw [hqdef]; field_simp; simp only [add_sub_cancel]
    rw [hs']
    simp only [VectorScheme.t_succ']
    push_cast
    nlinarith [hnq, hδR]
  have hs_le : s ≤ ((S.t n : ℚ) : ℝ) + ((S.δ : ℚ) : ℝ) := by
    have hs' : s = ((S.t₀ : ℚ) : ℝ) + q * ((S.δ : ℚ) : ℝ) := by
      rw [hqdef]; field_simp; simp only [add_sub_cancel]
    rw [hs']
    simp only [VectorScheme.t_succ']
    push_cast
    nlinarith [hqn, hδR]
  have hplR : S.plR s = (S.x n : ℝ^k)
      + (s - ((S.t n : ℚ) : ℝ)) • ((S.m (S.t n) (S.x n) : ℚ^k) : ℝ^k) := by
    simp only [VectorScheme.plR, ← hndef]
  rcases lt_or_eq_of_le hnN with hlt | heq
  · rw [hplR]
    refine le_trans (hcell n (by rw [hfloor]; exact Finset.mem_range.mpr hlt) s
        ⟨htn_le, hs_le⟩) ?_
    have hKcast : (((K : ℝ).toNNReal : NNReal) : ℝ) = (K : ℝ) := by
      simp only [Real.toNNReal]
      simp only [NNReal.coe_mk, sup_eq_left, Rat.cast_nonneg]
      exact_mod_cast hKne.le
    rw [hKcast]
    calc ‖y (S.t n) - (S.x n : ℝ^k)‖ * (1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) + A
        ≤ EBr n * (1 + (K : ℝ) * ((S.δ : ℚ) : ℝ)) + A := by
          have := hgrid' n (le_of_lt hlt)
          nlinarith [hδR, hKR]
      _ = EBr (n + 1) := hEBrec n
      _ ≤ EBr N := hEBmono (by omega)
  · subst heq
    have hsT : s = ((S.t n : ℚ) : ℝ) :=
      le_antisymm (by rw [htN]; exact hs.2) htn_le
    rw [hplR, hsT]
    simp only [sub_self, zero_smul, add_zero]
    exact hgrid' n le_rfl

end Vector

end ODE
