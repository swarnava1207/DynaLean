module

public import Mathlib
public import DynaLean.Defs
public import DynaLean.Comparison

@[expose] public section

/-! # Qualitative invariants ("rules") satisfied by a solution

Side information that a solution is known to satisfy *for structural reasons*, and that
can therefore be used to tighten a numerical enclosure without doing any extra
numerics. Each rule here is a region or a monotonicity property that the exact solution
can never leave:

* `ODE.solution_half_line` — if the field is nonnegative on the level `c` and the
  solution starts above `c`, it stays above `c` (an invariant half-line);
* `ODE.solution_monotone` — if the field is nonnegative along the solution, the
  solution is monotone;
* `ODE.solution_lyapunov_kind` — if the field points inward at `±R` (nonpositive above
  `R`, nonnegative below `-R`), the band `[-R, R]` is forward invariant.

`DynaLean.RulesBound` intersects each of these with the Euler error bound of
`DynaLean.EulerBound` to obtain enclosures that are strictly tighter than either source
alone.
-/

namespace ODE

/-- A lower barrier: the solution never falls below a level the field pushes it away
from.

If `y t₀ ≥ c`, the field is `K`-Lipschitz in state on `[t₀, T]`, and `f t c ≥ 0` there,
then `y t ≥ c` throughout `[t₀, T]`. Proved by comparing `y` against the constant
solution `c` of the zero field with `ODE.comparison_first_order`. -/
theorem solution_half_line
  (hy : SolutionExists f x₀ y t₀ T (Set.Icc t₀ T))
  (hc : y t₀ ≥ c) (hfc : ∀ t ∈ Set.Icc t₀ T, f t c ≥ 0)
  (hl : ∀ t ∈ Set.Icc t₀ T, LipschitzWith K (fun x => f t x))
  (ht : t₀ ≤ T) :
  ∀ t ∈ Set.Icc t₀ T, y t ≥ c := by
  set z := fun s ↦ c
  set g : ℝ → ℝ → ℝ := fun t x ↦ 0
  have hz : SolutionExists g c z t₀ T (Set.Icc t₀ T) := by
    apply And.intro (by grind)
    intro t ht
    simp only [g, z]
    apply hasDerivWithinAt_const
  have hg : ∀ t ∈ Set.Icc t₀ T, f t (z t) ≥ g t (z t) := by
    intro t ht
    simp only [g, z]
    exact hfc t ht
  have hcomp := comparison_first_order K hl z y ht (by rw [hy.1] at hc; grind) hg hz hy
  grind

/-- A solution whose field is nonnegative along it is monotone increasing.

Immediate from `monotoneOn_of_hasDerivWithinAt_nonneg`, since the derivative of `y` at
`t` *is* `f t (y t)`. The companion `DynaLean.RulesBound.monotone_bound` uses this to
propagate the best lower bound found so far to every later grid point. -/
theorem solution_monotone
  (hy : SolutionExists f x₀ y t₀ T (Set.Icc t₀ T))
  (hf : ∀ t ∈ Set.Icc t₀ T, f t (y t) ≥ 0)
  : MonotoneOn y (Set.Icc t₀ T) := by
  intro t₁ ht₁ t₂ ht₂ h12
  set f' := fun t ↦ f t (y t) with hf'
  apply monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc t₀ T) (convex_Icc t₀ T)
    (HasDerivWithinAt.continuousOn hy.2) (f' := f') _ _ ht₁ ht₂ h12
  · intro t ht
    have h1 := hy.2 t (interior_subset ht)
    rw [hf']
    simp only
    exact h1.mono (interior_subset)
  · intro t ht
    simp only [hf']
    exact hf t (interior_subset ht)

/-- Forward invariance of the band `[-R, R]` for an inward-pointing field.

If `f t x ≤ 0` for `x ≥ R` and `f t x ≥ 0` for `x ≤ -R` on `[t₀, T]`, and the solution
starts in `[-R, R]`, it never leaves.

The name refers to the Lyapunov-style argument: suppose the solution escapes, say
upwards. The last time `tf` at which it equals `R` exists (the escape set is closed and
bounded), beyond `tf` the solution is strictly above `R`, and the mean value theorem
produces a point in `(tf, t₁)` where the derivative is positive — contradicting
`f t x ≤ 0` for `x ≥ R`. The downward case is symmetric. -/
theorem solution_lyapunov_kind
  (hy : SolutionExists f x₀ y t₀ T (Set.Icc t₀ T))
  (hf : ∀ t ∈ Set.Icc t₀ T, (∀ x ≥ R, f t x ≤ 0) ∧ (∀ x ≤ -R, f t x ≥ 0))
  (hs : y t₀ ∈ Set.Icc (-R) R) :
  ∀ t ∈ Set.Icc t₀ T, y t ∈ Set.Icc (-R) R := by
  by_contra h
  simp only [Set.mem_Icc, and_imp, not_forall, not_and, not_le] at h
  let ⟨t₁, ht₁0, ht₁T, h₁⟩ := h
  have hset : Set.Icc t₀ t₁ = Set.uIcc t₀ t₁ := by
    simp only [Set.uIcc]
    grind
  by_cases h₂ : y t₁ < -R
  · set S := {t ∈ Set.Icc t₀ t₁ | y t = -R}
    have hS : S.Nonempty := by
      have this : ∃ t ∈ Set.uIcc t₀ t₁, y t = -R := by
        apply intermediate_value_uIcc
        · set f' := fun t ↦ f t (y t) with hf'
          apply HasDerivWithinAt.continuousOn (f' := f')
          intro t ht
          rw [hf']
          simp only
          rw [← hset]
          exact (hy.2 t (by grind)).mono (by grind)
        · simp only [Set.mem_uIcc]
          apply Or.inr
          exact And.intro h₂.le hs.1
      let ⟨t, ht, hyR⟩ := this
      rw [← hset] at ht
      exact ⟨t, ht, hyR⟩
    have hSb : BddAbove S := ⟨t₁, fun _ h => h.1.2⟩
    let tf := sSup S
    have htf : tf ∈ S := by
      apply IsClosed.csSup_mem (s := S) _ hS hSb
      have hS_eq : S = Set.Icc t₀ t₁ ∩ y ⁻¹' {-R} := rfl
      rw [hS_eq]
      apply ContinuousOn.preimage_isClosed_of_isClosed
      · intro x hx
        have hx' : x ∈ Set.Icc t₀ T := by grind [Set.uIcc_subset_Icc]
        exact (hy.2 x hx').continuousWithinAt.mono (by grind [Set.uIcc_subset_Icc])
      · exact isClosed_Icc
      · exact isClosed_singleton
    have htfR : y tf = -R := by grind
    have htfmax : ∀ s ∈ Set.Ioo tf t₁, y s < -R := by
      intro s hs
      by_contra hneg
      have hcont : ContinuousOn y (Set.Icc s t₁) := by
        intro x hx
        have hxT : x ∈ Set.Icc t₀ T := by grind [Set.uIcc_subset_Icc]
        exact (hy.2 x hxT).continuousWithinAt.mono (by grind [Set.uIcc_subset_Icc])
      have h_ivt : ∃ r ∈ Set.Icc s t₁, y r = -R := by
        have hseteq : Set.uIcc s t₁ = Set.Icc s t₁ := by grind [Set.uIcc]
        rw [← hseteq]
        apply intermediate_value_uIcc (by rw [← hseteq] at hcont; exact hcont)
        simp only [Set.mem_uIcc]
        apply Or.inr
        exact And.intro (by grind) (by grind)
      let ⟨r, hr, hyr⟩ := h_ivt
      have hrS : r ∈ S := by grind
      have hr_le : r ≤ tf := le_csSup hSb hrS
      have hslt : s ≤ tf := by grind
      grind
    set f' := fun t ↦ f t (y t) with hf'
    have hmvt : ∃ s ∈ Set.Ioo tf t₁, f' s = (y t₁ - y tf) / (t₁ - tf) := by
     apply exists_hasDerivAt_eq_slope
     · apply lt_of_le_of_ne htf.1.2
       grind
     · apply HasDerivWithinAt.continuousOn (f' := f')
       intro t ht
       rw [hf']
       simp only
       exact (hy.2 t (by grind)).mono (by grind)
     · intro t ht
       apply HasDerivWithinAt.hasDerivAt (s := Set.Ioo tf t₁) _ (Ioo_mem_nhds ht.1 ht.2)
       rw [hf']
       simp only
       exact (hy.2 t (by grind)).mono (by grind)
    let ⟨s, hs, hderiv⟩ := hmvt
    have hderneg : 0 ≥ f' s := by
      rw [hderiv]
      apply div_nonpos_of_nonpos_of_nonneg (by grind) (by grind)
    rw [hf'] at hderneg
    simp only at hderneg
    have hcontra : f s (y s) ≥ 0 := (hf s (by grind)).2 (y s) (htfmax s hs).le
    grind
  · specialize h₁ (by grind)
    set S := {t ∈ Set.Icc t₀ t₁ | y t = R}
    have hS : S.Nonempty := by
      have this : ∃ t ∈ Set.Icc t₀ t₁ , y t = R := by
        apply intermediate_value_Icc ht₁0
        · set f' := fun t ↦ f t (y t) with hf'
          apply HasDerivWithinAt.continuousOn (f' := f')
          intro t ht
          rw [hf']
          simp only
          exact (hy.2 t (by grind)).mono (by grind)
        · simp only [Set.mem_Icc]
          exact And.intro hs.2 h₁.le
      let ⟨t, ht, hyR⟩ := this
      exact ⟨t, ht, hyR⟩
    have hSb : BddAbove S := ⟨t₁, fun _ h => h.1.2⟩
    let tf := sSup S
    have htf : tf ∈ S := by
      apply IsClosed.csSup_mem (s := S) _ hS hSb
      have hS_eq : S = Set.Icc t₀ t₁ ∩ y ⁻¹' {R} := rfl
      rw [hS_eq]
      apply ContinuousOn.preimage_isClosed_of_isClosed
      · intro x hx
        have hx' : x ∈ Set.Icc t₀ T := by grind [Set.uIcc_subset_Icc]
        exact (hy.2 x hx').continuousWithinAt.mono (by grind [Set.uIcc_subset_Icc])
      · exact isClosed_Icc
      · exact isClosed_singleton
    have htfR : y tf = R := by grind
    have htfmax : ∀ s ∈ Set.Ioo tf t₁, y s > R := by
      intro s hs
      by_contra hneg
      have hcont : ContinuousOn y (Set.Icc s t₁) := by
        intro x hx
        have hxT : x ∈ Set.Icc t₀ T := by grind [Set.uIcc_subset_Icc]
        exact (hy.2 x hxT).continuousWithinAt.mono (by grind [Set.uIcc_subset_Icc])
      have h_ivt : ∃ r ∈ Set.Icc s t₁, y r = R := by
        apply intermediate_value_Icc (le_of_lt hs.2) hcont
        simp only [Set.mem_Icc]
        exact And.intro (by grind) (by grind)
      let ⟨r, hr, hyr⟩ := h_ivt
      have hrS : r ∈ S := by grind
      have hr_le : r ≤ tf := le_csSup hSb hrS
      have hslt : s ≤ tf := by grind
      grind
    set f' := fun t ↦ f t (y t) with hf'
    have hmvt : ∃ s ∈ Set.Ioo tf t₁, f' s = (y t₁ - y tf) / (t₁ - tf) := by
      apply exists_hasDerivAt_eq_slope
      · apply lt_of_le_of_ne htf.1.2
        grind
      · apply HasDerivWithinAt.continuousOn (f' := f')
        intro t ht
        rw [hf']
        simp only
        exact (hy.2 t (by grind)).mono (by grind)
      · intro t ht
        apply HasDerivWithinAt.hasDerivAt (s := Set.Ioo tf t₁) _ (Ioo_mem_nhds ht.1 ht.2)
        rw [hf']
        simp only
        exact (hy.2 t (by grind)).mono (by grind)
    let ⟨s, hs, hderiv⟩ := hmvt
    have hderpos : 0 ≤ f' s := by
      rw [hderiv]
      apply div_nonneg (by grind) (by grind)
    rw [hf'] at hderpos
    simp only at hderpos
    have hcontra : f s (y s) ≤ 0 := (hf s (by grind)).1 (y s) (htfmax s hs).le
    grind











end ODE
#check Set.Nonempty
#check exists_ratio_hasDerivAt_eq_ratio_slope
