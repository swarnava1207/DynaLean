import Mathlib
import DynaLean.Defs
import DynaLean.EulerScheme
import DynaLean.EulerBound
import DynaLean.Rules

/-!-/
namespace ODE


abbrev bound (n : ℕ) (ε K M δ : ℚ) := ((ε + M * δ / 2) * δ) * (((1 + K*δ) ^ n) - 1)/(K * δ)

def half_line_refine (S : Scheme) (ε c K M : ℚ) (n : ℕ) :=
  let Ln := S.x n - bound n ε K M S.δ
  let Un := S.x n + bound n ε K M S.δ
  ((max c Ln),Un)

def monotone_refine (S : Scheme) (ε K M : ℚ) (n : ℕ) :=
  let Ln := S.x n - bound n ε K M S.δ
  let Un := S.x n + bound n ε K M S.δ
  match n with
  | 0 => (Ln, Un)
  | n+1 =>
  (max (monotone_refine S ε K M n).1 Ln, Un)

def lyapunov_refine (S : Scheme) (ε R K M : ℚ) (n : ℕ) :=
  let Ln := S.x n - bound n ε K M S.δ
  let Un := S.x n + bound n ε K M S.δ
  ((max (-R) Ln), (min R Un))

section RefineProofs

variable {f : ℝ → ℝ → ℝ} {S : Scheme} {ε x₀ t₀ T K M : ℚ} (hMne : 0 < M) (hKne : 0 < K)
  (hT : t₀ < T)
  (hlip : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
  (hy : SolutionExists f x₀ y (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T))
  (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) T))
  (hm : ∀ t x : ℚ, |f t x - S.m t x| ≤ ε)
  (hiter : ∀ t ∈ Set.Ioo (t₀ : ℝ) T, |iteratedDeriv 2 y t| ≤ M)
  (hS : S.t₀ = t₀ ∧ S.x₀ = x₀)

include hMne hKne hT hlip hy hcont hm hiter hS

theorem half_line_bound (c : ℚ) (hc : y t₀ ≥ c)
  (hfc : ∀ t ∈ Set.Icc (t₀ : ℝ) T, f t c ≥ 0)
  : ∀ n ∈ Finset.range (⌊(T - t₀)/ S.δ⌋₊ + 1),
    y (S.t n) ∈ Set.Icc ((half_line_refine S ε c K M n).1 : ℝ) (half_line_refine S ε c K M n).2 :=
  by
  intro n hn
  have hrat := euler_bound_solution_rational M hMne (by exact_mod_cast hKne) hy hcont S hT hm hlip
                hiter hS n hn
  have hcomp := solution_half_line hy (by grind) hfc hlip (by exact_mod_cast hT.le)
  simp only [half_line_refine]
  rw [abs_le] at hrat
  constructor
  · push_cast
    apply max_le (hcomp (S.t n) (by grind [S.time_mem T (by grind) n (by grind)]))
    grind
  · push_cast
    grind

theorem monotone_bound (hf : ∀ t ∈ Set.Icc (t₀ : ℝ) T, f t (y t) ≥ 0)
  : ∀ n ∈ Finset.range (⌊(T - t₀)/ S.δ⌋₊ + 1),
    y (S.t n) ∈ Set.Icc ((monotone_refine S ε K M n).1 : ℝ) (monotone_refine S ε K M n).2 :=
  by
  intro n hn
  have hrat := euler_bound_solution_rational M hMne (by exact_mod_cast hKne) hy hcont S hT hm hlip
                hiter hS n hn
  have hcomp := solution_monotone hy hf
  induction n with
  | zero =>
    simp only [monotone_refine, Scheme.t, bound]
    simp only [Scheme.x, pow_zero, sub_self, mul_zero, zero_div, sub_zero, add_zero, Set.Icc_self,
      CharP.cast_eq_zero, zero_mul, Set.mem_singleton_iff]
    rw [hS.1, hS.2, hy.1]
  | succ m ih =>
    simp only [monotone_refine]
    constructor
    · push_cast
      apply max_le _ (by grind)
      specialize ih (by grind)
       (euler_bound_solution_rational M hMne (by exact_mod_cast hKne) hy hcont S hT hm hlip
                hiter hS m (by grind))
      have hmono : y (S.t m) ≤ y (S.t (m + 1)) := by
        apply hcomp (by grind [S.time_mem T (by grind) m (by grind)])
          (by grind [S.time_mem T (by grind) (m + 1) (by grind)])
        norm_cast
        simp only [Scheme.t, Nat.cast_add, Nat.cast_one, add_le_add_iff_left]
        ring_nf
        simp only [le_add_iff_nonneg_right]
        exact S.hδ.le
      grind
    · push_cast
      grind

theorem lyapunov_bound (R : ℚ) (hf : ∀ t ∈ Set.Icc (t₀ : ℝ) T, (∀ x ≥ (R : ℝ), f t x ≤ 0) ∧
  (∀ x ≤ (-R : ℝ), f t x ≥ 0))
  (hs : y t₀ ∈ Set.Icc (-R : ℝ) (R : ℝ))
  : ∀ n ∈ Finset.range (⌊(T - t₀)/ S.δ⌋₊ + 1),
    y (S.t n) ∈ Set.Icc ((lyapunov_refine S ε R K M n).1 : ℝ) (lyapunov_refine S ε R K M n).2 :=
  by
  intro n hn
  have hrat := euler_bound_solution_rational M hMne (by exact_mod_cast hKne) hy hcont S hT hm hlip
                hiter hS n hn
  have hcomp := solution_lyapunov_kind hy hf hs
  specialize hcomp (S.t n) (by grind [S.time_mem T (by grind) n (by grind)])
  simp only [lyapunov_refine]
  constructor
  · push_cast
    apply max_le (hcomp.1)
    grind
  · push_cast
    apply le_min (hcomp.2)
    grind

end RefineProofs

end ODE
