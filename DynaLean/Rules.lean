module

public import Mathlib
public import DynaLean.Defs
public import DynaLean.Comparison

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

@[expose] public section

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

/-! ## Scalar barrier lemmas, for use in the vector case

The three scalar rules above all route through `ODE.comparison_first_order`, which
requires the vector field to be Lipschitz in its state argument. DynaLean has no vector
analogue of that comparison theorem, so the vector rules below are proved instead by a
direct "last crossing" argument, isolated here as two statements about an arbitrary
differentiable real function.

This is a change of hypothesis, not a weakening of the conclusion. Where
`ODE.solution_half_line` assumes `f t c ≥ 0` only *at* the level `c` and pays for that
with a Lipschitz constant, `ODE.ge_of_deriv_nonneg_of_le` assumes the sign condition
throughout the region `g t ≤ c` and needs no Lipschitz hypothesis at all. Some such
strengthening is unavoidable once Lipschitz continuity is dropped: `g t = -t ^ 3`
satisfies `g 0 = 0` and `g' 0 = 0`, yet leaves `[0, ∞)` immediately.

Note that the hypothesis `ODE.solution_lyapunov_kind` already uses — a sign condition on
the whole region `x ≥ R` rather than only at `x = R` — is of exactly this region form,
so the vector Lyapunov rule below is a faithful analogue of the scalar one. -/

/-- A lower barrier for a differentiable real function.

If `g` has derivative `g' t` at every time of `[t₀, T]`, starts at or above the level
`c`, and has nonnegative derivative everywhere it is at or below `c`, then it never
drops below `c`.

The proof is the "last crossing" argument. If `g t₁ < c`, the intermediate value theorem
gives a time in `[t₀, t₁]` at which `g = c`; the supremum `tf` of those times is itself
one of them, because the level set is closed and bounded; `g < c` throughout
`(tf, t₁)` by maximality; and the mean value theorem on `[tf, t₁]` then produces an
interior point with strictly negative derivative, contradicting the hypothesis. -/
theorem ge_of_deriv_nonneg_of_le {g g' : ℝ → ℝ} {t₀ T c : ℝ}
    (hg : ∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt g (g' t) (Set.Icc t₀ T) t)
    (hc : c ≤ g t₀)
    (hd : ∀ t ∈ Set.Icc t₀ T, g t ≤ c → 0 ≤ g' t) :
    ∀ t ∈ Set.Icc t₀ T, c ≤ g t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₁, ht₁, h₁⟩ := hcon
  have ht₀t₁ : t₀ ≤ t₁ := ht₁.1
  have ht₁T : t₁ ≤ T := ht₁.2
  have hsub : Set.Icc t₀ t₁ ⊆ Set.Icc t₀ T := Set.Icc_subset_Icc le_rfl ht₁T
  have hcont : ContinuousOn g (Set.Icc t₀ t₁) := fun x hx =>
    ((hg x (hsub hx)).continuousWithinAt).mono hsub
  set S := {t ∈ Set.Icc t₀ t₁ | g t = c}
  have hSne : S.Nonempty := by
    obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc' ht₀t₁ hcont ⟨h₁.le, hc⟩
    exact ⟨r, hr, hgr⟩
  have hSb : BddAbove S := ⟨t₁, fun _ h => h.1.2⟩
  let tf := sSup S
  have htf : tf ∈ S := by
    apply IsClosed.csSup_mem (s := S) _ hSne hSb
    have hS_eq : S = Set.Icc t₀ t₁ ∩ g ⁻¹' {c} := rfl
    rw [hS_eq]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have htfc : g tf = c := htf.2
  have htfmem : tf ∈ Set.Icc t₀ t₁ := htf.1
  have htflt : tf < t₁ := by
    rcases lt_or_eq_of_le htfmem.2 with h | h
    · exact h
    · rw [h] at htfc; linarith
  have hbelow : ∀ s ∈ Set.Ioo tf t₁, g s < c := by
    intro s hs
    by_contra hneg
    push Not at hneg
    have hss : Set.Icc s t₁ ⊆ Set.Icc t₀ t₁ :=
      Set.Icc_subset_Icc (le_trans htfmem.1 hs.1.le) le_rfl
    obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc' hs.2.le (hcont.mono hss) ⟨h₁.le, hneg⟩
    have hrS : r ∈ S := ⟨hss hr, hgr⟩
    have hrle : r ≤ tf := le_csSup hSb hrS
    linarith [hr.1, hs.1]
  have hmvt : ∃ s ∈ Set.Ioo tf t₁, g' s = (g t₁ - g tf) / (t₁ - tf) := by
    refine exists_hasDerivAt_eq_slope g g' htflt
      (hcont.mono (Set.Icc_subset_Icc htfmem.1 le_rfl)) ?_
    intro s hs
    refine HasDerivWithinAt.hasDerivAt ?_ (Ioo_mem_nhds hs.1 hs.2)
    exact (hg s (hsub ⟨le_trans htfmem.1 hs.1.le, hs.2.le⟩)).mono
      (fun z hz => hsub ⟨le_trans htfmem.1 hz.1.le, hz.2.le⟩)
  obtain ⟨s, hs, hslope⟩ := hmvt
  have hsmem : s ∈ Set.Icc t₀ T := hsub ⟨le_trans htfmem.1 hs.1.le, hs.2.le⟩
  have h0 : 0 ≤ g' s := hd s hsmem (hbelow s hs).le
  rw [hslope, htfc] at h0
  have hlt : (g t₁ - c) / (t₁ - tf) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by linarith)
  linarith

/-- An upper barrier for a differentiable real function: the mirror image of
`ODE.ge_of_deriv_nonneg_of_le`, obtained from it by applying that lemma to `-g`.

If `g` starts at or below `c` and has nonpositive derivative everywhere it is at or
above `c`, then it never rises above `c`. -/
theorem le_of_deriv_nonpos_of_ge {g g' : ℝ → ℝ} {t₀ T c : ℝ}
    (hg : ∀ t ∈ Set.Icc t₀ T, HasDerivWithinAt g (g' t) (Set.Icc t₀ T) t)
    (hc : g t₀ ≤ c)
    (hd : ∀ t ∈ Set.Icc t₀ T, c ≤ g t → g' t ≤ 0) :
    ∀ t ∈ Set.Icc t₀ T, g t ≤ c := by
  intro t ht
  have hneg : ∀ s ∈ Set.Icc t₀ T,
      HasDerivWithinAt (fun u => -g u) ((fun u => -g' u) s) (Set.Icc t₀ T) s :=
    fun s hs => (hg s hs).neg
  have h := ge_of_deriv_nonneg_of_le (g := fun u => -g u) (g' := fun u => -g' u) (c := -c)
    hneg (by simpa using hc)
    (fun s hs hle => by
      have hcs : c ≤ g s := by simpa using hle
      simpa using hd s hs hcs) t ht
  simpa using h

/-! ## The vector case

Everything below transports the scalar rules to `ℝ^n`-valued solutions by reading off a
single coordinate. The point is that for a fixed `i : Fin n` the real function
`t ↦ y t i` has derivative `(f t (y t)) i` (`ODE.hasDerivWithinAt_coord`), so the
barrier lemmas apply to it directly.

Coordinates rather than general linear functionals, because that is what the numerical
side needs: `DynaLean.RulesBound` turns the ball enclosure
`‖y tₙ - xₙ‖ ≤ bound n` coming from `ODE.euler_bound_solution_rational_vector` into a
*box* by projecting onto each coordinate, and the rules below refine that box
coordinate by coordinate. `ODE.solution_mem_box_vector` is the resulting statement:
forward invariance of an axis-aligned box.

Note that none of these generalizations is available coordinatewise "for free": a
coordinate `y t i` of a vector solution is not itself the solution of a scalar ODE,
since its velocity `(f t (y t)) i` depends on all the other coordinates. That is exactly
why the barrier lemmas above are stated for a function with a prescribed derivative
rather than for a solution of an equation. -/

section Vector

variable {n : ℕ} {f : ℝ → (ℝ^n) → ℝ^n} {x₀ : ℝ^n} {y : ℝ → ℝ^n} {t₀ T : ℝ}

/-- Read off one coordinate of a vector-valued derivative.

If the curve `z : ℝ → ℝ^n` has derivative `z'` within `s` at `t`, then the real function
`u ↦ z u i` has derivative `z' i`. Immediate from the fact that the coordinate
projection `EuclideanSpace.proj i` is a continuous linear map. -/
theorem hasDerivWithinAt_coord {z : ℝ → ℝ^n} {z' : ℝ^n} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt z z' s t) (i : Fin n) :
    HasDerivWithinAt (fun u => z u i) (z' i) s t := by
  have hp : HasFDerivAt (𝕜 := ℝ) (EuclideanSpace.proj i : (ℝ^n) →L[ℝ] ℝ)
      (EuclideanSpace.proj i : (ℝ^n) →L[ℝ] ℝ) (z t) :=
    ContinuousLinearMap.hasFDerivAt _
  simpa [Function.comp_def] using hp.comp_hasDerivWithinAt t h

/-- The derivative of a single coordinate of a vector ODE solution. -/
theorem SolutionExistsVector.coord_hasDerivWithinAt
    (hy : SolutionExistsVector f x₀ y t₀ T (Set.Icc t₀ T)) (i : Fin n) :
    ∀ t ∈ Set.Icc t₀ T,
      HasDerivWithinAt (fun u => y u i) ((f t (y t)) i) (Set.Icc t₀ T) t :=
  fun t ht => hasDerivWithinAt_coord (hy.2 t ht) i

/-- A lower barrier in one coordinate: the solution never leaves the half-space
`{x | c ≤ x i}`.

The `ℝ^n` analogue of `ODE.solution_half_line`. The level `c` of the scalar statement
becomes a half-space with axis-aligned boundary, and — see the discussion above — the
sign hypothesis is imposed on the whole region `x i ≤ c` rather than only on its
boundary, which removes the need for any Lipschitz assumption. -/
theorem solution_half_space_vector (i : Fin n) {c : ℝ}
    (hy : SolutionExistsVector f x₀ y t₀ T (Set.Icc t₀ T))
    (hc : c ≤ y t₀ i)
    (hfc : ∀ t ∈ Set.Icc t₀ T, ∀ x : ℝ^n, x i ≤ c → 0 ≤ (f t x) i) :
    ∀ t ∈ Set.Icc t₀ T, c ≤ y t i :=
  ge_of_deriv_nonneg_of_le (hy.coord_hasDerivWithinAt i) hc
    (fun t ht hle => hfc t ht (y t) hle)

/-- A coordinate of the solution is monotone when that coordinate of the velocity is
nonnegative along the trajectory.

The `ℝ^n` analogue of `ODE.solution_monotone`; like the scalar version it is immediate
from `monotoneOn_of_hasDerivWithinAt_nonneg`, here applied to `t ↦ y t i`. -/
theorem solution_monotone_vector (i : Fin n)
    (hy : SolutionExistsVector f x₀ y t₀ T (Set.Icc t₀ T))
    (hf : ∀ t ∈ Set.Icc t₀ T, 0 ≤ (f t (y t)) i) :
    MonotoneOn (fun t => y t i) (Set.Icc t₀ T) := by
  intro t₁ ht₁ t₂ ht₂ h12
  refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc t₀ T) (convex_Icc t₀ T)
    (HasDerivWithinAt.continuousOn (hy.coord_hasDerivWithinAt i))
    (f' := fun t => (f t (y t)) i) ?_ ?_ ht₁ ht₂ h12
  · intro t ht
    exact ((hy.coord_hasDerivWithinAt i) t (interior_subset ht)).mono interior_subset
  · intro t ht
    exact hf t (interior_subset ht)

/-- Forward invariance of the slab `{x | -R ≤ x i ≤ R}` for a field that points inward
on both of its faces.

The `ℝ^n` analogue of `ODE.solution_lyapunov_kind`, with the same shape of hypothesis:
the sign conditions are imposed on the regions `R ≤ x i` and `x i ≤ -R`, not merely on
the two boundary hyperplanes. Both halves come from the barrier lemmas. -/
theorem solution_lyapunov_kind_vector (i : Fin n) {R : ℝ}
    (hy : SolutionExistsVector f x₀ y t₀ T (Set.Icc t₀ T))
    (hf : ∀ t ∈ Set.Icc t₀ T, (∀ x : ℝ^n, R ≤ x i → (f t x) i ≤ 0) ∧
                              (∀ x : ℝ^n, x i ≤ -R → 0 ≤ (f t x) i))
    (hs : y t₀ i ∈ Set.Icc (-R) R) :
    ∀ t ∈ Set.Icc t₀ T, y t i ∈ Set.Icc (-R) R := by
  have hlow := ge_of_deriv_nonneg_of_le (hy.coord_hasDerivWithinAt i) hs.1
    (fun t ht hle => (hf t ht).2 (y t) hle)
  have hhigh := le_of_deriv_nonpos_of_ge (hy.coord_hasDerivWithinAt i) hs.2
    (fun t ht hge => (hf t ht).1 (y t) hge)
  exact fun t ht => ⟨hlow t ht, hhigh t ht⟩

/-- Forward invariance of an axis-aligned box.

The genuinely `n`-dimensional statement: if on every face the field points back into the
box `∏ i, [A i, B i]`, then a solution starting in the box stays in it. Applying
`ODE.solution_lyapunov_kind_vector` in each coordinate, with the faces allowed to sit at
independent levels instead of at `±R`.

This is the invariant used by `DynaLean.RulesBound` to tighten the box enclosure that
the Euler bound provides. -/
theorem solution_mem_box_vector (A B : Fin n → ℝ)
    (hy : SolutionExistsVector f x₀ y t₀ T (Set.Icc t₀ T))
    (hf : ∀ t ∈ Set.Icc t₀ T, ∀ i : Fin n,
            (∀ x : ℝ^n, B i ≤ x i → (f t x) i ≤ 0) ∧
            (∀ x : ℝ^n, x i ≤ A i → 0 ≤ (f t x) i))
    (hs : ∀ i : Fin n, y t₀ i ∈ Set.Icc (A i) (B i)) :
    ∀ t ∈ Set.Icc t₀ T, ∀ i : Fin n, y t i ∈ Set.Icc (A i) (B i) := by
  intro t ht i
  have hlow := ge_of_deriv_nonneg_of_le (hy.coord_hasDerivWithinAt i) (hs i).1
    (fun u hu hle => ((hf u hu) i).2 (y u) hle)
  have hhigh := le_of_deriv_nonpos_of_ge (hy.coord_hasDerivWithinAt i) (hs i).2
    (fun u hu hge => ((hf u hu) i).1 (y u) hge)
  exact ⟨hlow t ht, hhigh t ht⟩

end Vector








end ODE
#check Set.Nonempty
#check exists_ratio_hasDerivAt_eq_ratio_slope
