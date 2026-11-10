module

public import Mathlib
public import DynaLean.Defs
public meta import DynaLean.EulerScheme
import DynaLean.EulerScheme
public import DynaLean.EulerBound

/-! # Refining a numerical estimate with prior one-sided bounds

Where `DynaLean.RulesBound` specializes to three particular invariants, this module
handles the generic situation: the user already knows an upper bound `b` and/or a lower
bound `a` for the solution over the whole of `[t₀, T]`, each of which may be absent.
Absence is modelled by `Option ℚ`, with `none` meaning "no information", so a single
code path covers all four combinations.

`ODE.refinement` intersects the Euler interval `xₙ ± bound n` with `[a, b]` and returns
the *midpoint* of the result, i.e. a single best estimate rather than an interval. It
returns `none` exactly when the prior bounds are contradictory (`a > b`).

`ODE.refinement_satisfy` is the soundness theorem: the returned estimate respects both
prior bounds and is within the Euler error radius of the exact solution. Narrowing the
interval can only move the midpoint closer, which is why the *same* radius still works.
`ODE.convex_rule_exists_refinement` repackages that as a plain existence statement.

The final group (`ODE.refinement_monotone`, `ODE.refinement_monotone_satisfy`) is the
monotone variant, where the estimate at step `n + 1` is the running maximum of the
Euler iterates — legitimate when the exact solution is known to be increasing along the
grid.
-/

@[expose] public section

namespace ODE

/-- `Rule S x t₀ T` says the trajectory `x` stays inside the region `S` on `[t₀, T]`.

The generic shape of a qualitative invariant; the concrete instances live in
`DynaLean.Rules`. -/
def Rule (S : Set ℝ) (x : ℝ → ℝ) (t₀ T : ℝ) := ∀ t ∈ Set.Icc t₀ T, x t ∈ S

/-- An optional rational bound: `none` means "no bound known", `some q` means the
bound `q`.

Using `Option` rather than `ℚ` is what lets `ODE.refinement` treat one-sided and
two-sided prior knowledge uniformly. -/
abbrev bound := Option ℚ

/-- `BdAbv y b` holds when `y` respects the optional upper bound `b`; vacuously true
for `none`. -/
def BdAbv (y : ℝ) (b : bound) : Prop :=
  match b with
  | none => True
  | some b => y ≤ b

/-- `BdBlw y b` holds when `y` respects the optional lower bound `b`; vacuously true
for `none`. -/
def BdBlw (y : ℝ) (b : bound) : Prop :=
  match b with
  | none => True
  | some b => y ≥ b

/-- `BdAbvF x t₀ T b`: the function `x` respects the optional upper bound `b` at every
time of `[t₀, T]`. -/
def BdAbvF (x : ℝ → ℝ) (t₀ T : ℝ) (b : bound) : Prop := ∀ t ∈ Set.Icc t₀ T, BdAbv (x t) b

/-- `BdBlwF x t₀ T b`: the function `x` respects the optional lower bound `b` at every
time of `[t₀, T]`. -/
def BdBlwF (x : ℝ → ℝ) (t₀ T : ℝ) (b : bound) : Prop := ∀ t ∈ Set.Icc t₀ T, BdBlw (x t) b


/-- Refine the `n`-th Euler iterate using optional prior bounds `a` (lower) and `b`
(upper).

Intersects the Euler interval `xₙ ± (ε + M δ/2) δ ((1 + K δ)ⁿ - 1)/(K δ)` with `[a, b]`
and returns the midpoint of the intersection. Returns `none` precisely when both prior
bounds are present and inconsistent (`a > b`), a case `ODE.refinement_satisfy` shows
cannot arise for a genuine solution.

The `hn : n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1)` argument is not used in the
computation; it is there to keep the function from being applied outside the grid
covering `[t₀, T]`, where the error bound would not hold. -/
def refinement (S : Scheme) (ε M K t₀ T : ℚ) (a b : bound) (n : ℕ)
  : n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1) → Option ℚ :=
  fun _ =>
  match a, b with
  |some a, some b => if a > b then none
    else let bound := (ε + M * S.δ/2) * S.δ * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ)
    let lwb := max (S.x n - bound) a
    let upb := min (S.x n + bound) b
    some ((lwb + upb)/2)
  | _, _ =>
    let bound := (ε + M * S.δ/2) * S.δ * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ)
    let lwb := match a with
      | none => S.x n - bound
      | some a => max (S.x n - bound) a
    let upb := match b with
      | none => S.x n + bound
      | some b => min (S.x n + bound) b
    some ((lwb + upb)/2)


/-- Soundness of `ODE.refinement`.

Under the hypotheses of `ODE.euler_bound_solution_rational`, and given that the exact
solution `x` really does respect the prior bounds `a` and `b` on `[t₀, T]`, the call
`refinement S ε M K t₀ T a b n hn`

* is never `none` — contradictory priors are impossible for an actual solution; and
* returns a rational `z` that respects both priors and satisfies
  `|z - x (S.t n)| ≤ (ε + M δ/2) δ ((1 + K δ)ⁿ - 1)/(K δ)`.

The error radius is unchanged from the unrefined Euler bound: clipping the interval
and then taking its midpoint can only shrink the distance to the solution, since the
solution lies in the clipped interval too. -/
theorem refinement_satisfy {f : ℝ → ℝ → ℝ} {K ε M x₀ t₀ T : ℚ} {S : Scheme}
    (hx : SolutionExists f x₀ x t₀ T (Set.Icc (t₀ : ℝ) T)) (hMne : M > 0) (hK : K > (0 : ℝ))
    (hcont : ContDiffOn ℝ 2 x (Set.Icc (t₀ : ℝ) T)) (hT : t₀ < T)
    (hlip : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal fun y => f t y)
    (hm : ∀ t y : ℚ, |f t y - S.m t y| ≤ ε)
    (hiter : ∀ t ∈ Set.Ioo (t₀:ℝ) T, |iteratedDeriv 2 x t| ≤ M)
    (hS : S.t₀ = t₀ ∧ S.x₀ = x₀)
    (hb : BdAbvF x t₀ T b) (ha : BdBlwF x t₀ T a)
    {n} (hn : n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1))
    : match refinement S ε M K t₀ T a b n hn with
      | none => False
      | some z => BdAbv z b ∧ BdBlw z a ∧ |z - x (S.t n)| ≤
        ((ε + M * S.δ/2) * S.δ * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ)) := by
        set bound := (ε + M * S.δ/2) * S.δ * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ) with hbound
        have hboundR : (bound : ℝ) = (ε + M * S.δ/2) * (S.δ : ℝ) * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ)
          := by exact_mod_cast rfl
        have hTR : t₀ < (T : ℝ) := by exact_mod_cast hT
        have heuler := euler_bound_solution_rational M hMne hK hx hcont S hT hm hlip hiter hS n hn
        rw [abs_le, ← hboundR] at heuler
        match h : refinement S ε M K t₀ T a b n hn with
        | none => match a, b with
                 |some a, some b =>
                  have h1 : (a : ℝ) ≤ b := by
                    apply le_trans
                    · exact ha t₀ (by grind)
                    · exact hb t₀ (by grind)
                  simp only
                  simp only [refinement, gt_iff_lt, ite_eq_left_iff, not_lt, reduceCtorEq,
                    imp_false, not_le] at h
                  have hR : (b : ℝ) < a := by exact_mod_cast h
                  grind
                  | none, some b =>
                    simp only
                    simp [refinement] at h
                  | some a, none =>
                    simp only
                    simp [refinement] at h
                  | none, none =>
                    simp only
                    simp [refinement] at h
        | some z =>
        simp only
        simp only [refinement] at h
        set lwb := match a with
          | none => S.x n - bound
          | some a => max (S.x n - bound) a with hlwb
        set upb := match b with
          | none => S.x n + bound
          | some b => min (S.x n + bound) b with hupb
        have h' : (lwb + upb)/2 = z := by
          match a, b with
          | some a, some b =>
            simp only [hlwb, hupb]
            have h1 : (a : ℝ) ≤ b := by
              apply le_trans
              · exact ha t₀ (by grind)
              · exact hb t₀ (by grind)
            simp only at h
            rw [ite_eq_right] at h
            · simp only [Option.some.injEq] at h
              rw [← hbound] at h
              exact h
            · simp only [not_lt]; exact_mod_cast h1
          | none, some b =>
            simp only [Option.some.injEq] at h
            grind
          | some a, none =>
            simp only [Option.some.injEq] at h
            grind
          | none, none =>
            simp only [Option.some.injEq] at h
            grind
        have this : x (S.t n) ∈ Set.Icc (lwb : ℝ) upb := by
          constructor
          · match a with
            | none => simp only [hlwb]; push_cast; grind
            | some a => simp only [hlwb]; push_cast;
                        apply max_le (by grind) (ha (S.t n)
                        (by rw [← hS.1]; exact Scheme.time_mem S T (by grind) n (by grind)))
          · match  b with
            | none => simp only [hupb]; push_cast; grind
            | some b => simp only [hupb]; push_cast;
                        rw [← min_self (a := x (S.t n))]
                        apply min_le_min (c := x (S.t n)) (d := x (S.t n))
                          (by grind) (hb (S.t n)
                          (by rw [← hS.1]; exact Scheme.time_mem S T (by grind) n (by grind)))
        have hend : (lwb : ℝ) ≤ upb := by
          apply le_trans this.1 this.2
        set b2 := max (z- lwb) (upb - z) with hb2
        have : |z - x (S.t n)| ≤ b2 := by
          rw [abs_le]
          constructor
          · have h1 : (z - upb : ℝ) ≤ (z - x (S.t n)) := by
              apply sub_le_sub_left
              exact this.2
            apply le_trans _ h1
            rw [← neg_neg (a := (z:ℝ) - upb)]
            apply neg_le_neg
            norm_cast
            grind
          · have h2 : z - x (S.t n) ≤ (z - (lwb : ℝ)):= by
              apply add_le_add_right
              exact neg_le_neg this.1
            apply le_trans h2 _
            norm_cast
            grind
        have hznew : lwb ≤ z ∧ z ≤ upb := by
          constructor
          · rw [← h']
            field_simp
            rw [mul_comm,two_mul]
            apply add_le_add_right (by exact_mod_cast hend)
          · rw [← h']
            field_simp
            rw [mul_comm,two_mul]
            apply add_le_add_left (by exact_mod_cast hend)
        rw [← h'] at hb2
        ring_nf at hb2
        simp only [max_self] at hb2
        apply And.intro (by simp only [BdAbv]; norm_cast; grind)
        apply And.intro (by simp only [BdBlw]; norm_cast; grind)
        rw [← hboundR]
        apply le_trans this
        rw [hb2]
        have new : upb / 2 - lwb / 2 = lwb * (-1 / 2) + upb * (1 / 2) := by ring
        rw [← new]
        norm_cast
        field_simp
        match a, b with
        | none, none => grind
        | none, some b => grind
        | some a, none => grind
        | some a, some b => grind


/-- Existence form of `ODE.refinement_satisfy`.

Restates the soundness theorem without mentioning the `Option` returned by
`ODE.refinement`: at every grid point there simply *exists* a rational estimate `z`
respecting both prior bounds and within the Euler error radius of the solution.
Convenient when the caller does not care how `z` was computed. -/
theorem convex_rule_exists_refinement {K ε M x₀ t₀ T : ℚ} {S : Scheme}
    (hx : SolutionExists f x₀ x t₀ T (Set.Icc (t₀ : ℝ) T)) (hMne : M > 0) (hK : K > (0 : ℝ))
    (hcont : ContDiffOn ℝ 2 x (Set.Icc (t₀ : ℝ) T)) (hT : t₀ < T)
    (hlip : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal fun y => f t y)
    (hm : ∀ t y : ℚ, |f t y - S.m t y| ≤ ε)
    (hiter : ∀ t ∈ Set.Ioo (t₀:ℝ) T, |iteratedDeriv 2 x t| ≤ M)
    (hS : S.t₀ = t₀ ∧ S.x₀ = x₀)
    (hb : BdAbvF x t₀ T b) (ha : BdBlwF x t₀ T a)
    : ∀ n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1),
    ∃ z : ℚ, BdAbv z b ∧ BdBlw z a ∧ |z - x (S.t n)| ≤ (ε + M * S.δ/2) *
    (S.δ : ℝ) * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ) := by
        intro n hn
        have href := refinement_satisfy hx hMne hK hcont hT hlip hm hiter hS hb ha hn
        have hTR : (t₀ : ℝ) < (T : ℝ) := by exact_mod_cast hT
        match h :refinement S ε M K t₀ T a b n hn with
        | none => simp only [h] at href
        | some z =>
          simp only [h] at href
          exists z


/-- The monotone estimate: the running maximum of the Euler iterates up to step `n`.

Appropriate when the exact solution is known to be increasing along the grid; then
replacing `xₙ` by `max x₀ ... xₙ` can only move the estimate towards the solution.
Soundness is `ODE.refinement_monotone_satisfy`. -/
def refinement_monotone (S : Scheme) (ε M K t₀ T : ℚ) (n : ℕ)
  (hn : n ∈ Finset.range (⌊(T - t₀) / S.δ⌋₊ + 1)) : ℚ :=
  match n with
  | 0 => S.x₀
  | n + 1 =>
    max (S.x (n + 1)) (refinement_monotone S ε M K t₀ T n (by grind))


/-- Taking a maximum does not degrade an error bound, provided the targets are ordered.

If `a` approximates `y` to within `p`, `w` approximates `Y` to within `q`, and
`y ≤ Y`, then `max a w` approximates `Y` to within `max p q`. This is the induction
step behind `ODE.refinement_monotone_satisfy`. -/
lemma ineq {a y p w Y q : ℝ} (h : |a - y| ≤ p) (g : |w - Y| ≤ q) (k : y ≤ Y)
  : |max a w - Y| ≤ max p q := by
  by_cases h' : max a w = a
  · rw [h']
    grind
  · grind

/-- Soundness of `ODE.refinement_monotone`.

Assuming additionally that the exact solution is increasing along the grid
(`hxn : x (S.t n) ≤ x (S.t (n+1))`), the running maximum

* is itself monotone in `n`, and
* stays within the usual Euler error radius
  `(ε + M δ/2) δ ((1 + K δ)ⁿ - 1)/(K δ)` of the solution.

The error radius survives because it is monotone in `n` (so `max` of two radii is the
later one) and because of the elementary `ODE.ineq`. -/
theorem refinement_monotone_satisfy {K ε M x₀ t₀ T : ℚ} {S : Scheme}
    (hx : SolutionExists f x₀ x t₀ T (Set.Icc (t₀ : ℝ) T)) (hMne : M > 0) (hK : K > (0 : ℝ))
    (hcont : ContDiffOn ℝ 2 x (Set.Icc (t₀ : ℝ) T)) (hT : t₀ < T)
    (hlip : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal fun y => f t y)
    (hm : ∀ t y : ℚ, |f t y - S.m t y| ≤ ε)
    (hiter : ∀ t ∈ Set.Ioo (t₀:ℝ) T, |iteratedDeriv 2 x t| ≤ M)
    (hxn : ∀ n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊), x (S.t n) ≤ x (S.t (n + 1)))
    (hS : S.t₀ = t₀ ∧ S.x₀ = x₀) (hn' : n + 1 ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1)) :
    refinement_monotone S ε M K t₀ T n (by grind) ≤ refinement_monotone S ε M K t₀ T (n + 1) hn'
    ∧ |refinement_monotone S ε M K t₀ T n (by grind) - x (S.t n)| ≤
    (ε + M * S.δ/2) * (S.δ : ℝ) * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ)
    := by
    have heps : (0 : ℝ) ≤ (ε : ℝ) := le_trans (b := |f 0 0 - S.m 0 0|) (by grind)
                                              (by exact_mod_cast hm 0 0)
    have hδ : 0 < S.δ := S.hδ
    have hKq : 0 < K := by exact_mod_cast hK
    have hepsQ : (0 : ℚ) ≤ ε := by exact_mod_cast heps
    constructor
    · match h : n with
      | 0 => simp only [refinement_monotone, Scheme.x, Scheme.t, CharP.cast_eq_zero, zero_mul,
      add_zero, le_max_iff, le_add_iff_nonneg_right, Std.le_refl,
      or_true]
      | m + 1 =>
        set em := refinement_monotone S ε M K t₀ T (m + 1) (by grind) with hem
        unfold refinement_monotone
        rw [← hem]
        grind
    · set bound := (ε + M * S.δ/2) * S.δ * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ) with hbound
      have hboundR : (bound : ℝ) = (ε + M * S.δ/2) * (S.δ : ℝ) * (((1 + K*S.δ) ^ n) - 1)/(K * S.δ)
        := by exact_mod_cast rfl
      rw [← hboundR]
      induction n with
      | zero =>
        simp only [refinement_monotone, Scheme.t, CharP.cast_eq_zero, zero_mul, add_zero]
        rw [hS.1, hS.2, hx.1]
        simp only [sub_self, abs_zero, Rat.cast_nonneg]
        simp [bound]
      | succ m ih =>
        specialize ih (by grind)
        simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_sub,
          Rat.cast_pow, Rat.cast_one, Scheme.t, Rat.cast_natCast, ge_iff_le,
          forall_const] at ih
        set bound' := (ε + M * S.δ/2) * S.δ * (((1 + K*S.δ) ^ m) - 1)/(K * S.δ) with hbound'
        have hboundR' : (bound' : ℝ) =
        (ε + M * S.δ/2) * (S.δ : ℝ) * (((1 + K*S.δ) ^ m) - 1)/(K * S.δ)
          := by exact_mod_cast rfl
        rw [← hboundR'] at ih
        have this : refinement_monotone S ε M K t₀ T (m + 1) (by grind)
        = max (refinement_monotone S ε M K t₀ T m (by grind)) (S.x (m + 1)) := by
          simp only [refinement_monotone]
          grind
        rw [this]
        have this2 : (bound : ℝ) = max (bound' : ℝ) (bound : ℝ) := by
          simp only [hboundR, hboundR']
          rw [max_eq_right]
          field_simp
          gcongr
          · simp only [le_add_iff_nonneg_right]; positivity
          · grind
        rw [this2]
        push_cast
        apply ineq (y := x (S.t m)) (Y := x (S.t (m + 1)))
        · simp only [Scheme.t, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
          grind
        · have hwant := euler_bound_solution_rational M hMne hK hx hcont S hT hm hlip hiter hS
            (m + 1) (by grind)
          rw [← hboundR] at hwant
          grind
        · specialize hxn m (by grind)
          grind

/-! ## Worked example

A throwaway scheme used only by the `#eval` below, to show the refinement machinery
actually computing. -/

/-- Example scheme: `δ = 1`, `t₀ = 0`, `x₀ = 1`, `m t y = y`, so `xₙ = 2ⁿ`. -/
def egScheme : Scheme := {
  t₀ := 0
  x₀ := 1
  δ := 1
  m := fun t y => y
  hδ := by grind
}

-- Refine the third iterate of `egScheme` against the prior bounds `0 ≤ x ≤ 2`.
#eval refinement egScheme 1 1 1 0 5 (some 0) (some 2) 3 (by simp only [sub_zero, egScheme, div_one,
  Nat.floor_ofNat, Nat.reduceAdd, Finset.mem_range, Nat.reduceLT])
end ODE
