import Mathlib
import DynaLean.Defs
open Set Filter
#print IsPicardLindelof
#check IsCompact.exists_bound_of_continuousOn
#print NNReal.coe_nonneg
#check LipschitzWith.lipschitzOnWith
#check div_le_div_right'
#search "i + 1 ∈ Finset.range N => i in Finset.range N?"

namespace ODE
theorem SolutionExists.shrink {f : ℝ → ℝ → ℝ} {y : ℝ} {x : ℝ → ℝ} {a b b' : ℝ}
    (h : SolutionExists f y x a b (Set.Icc a b)) (hb' : b' ≤ b) :
    SolutionExists f y x a b' (Set.Icc a b') :=
  ⟨h.1, fun s hs => (h.2 s ⟨hs.1, hs.2.trans hb'⟩).mono (Set.Icc_subset_Icc le_rfl hb')⟩

/-- Glue a solution on `[a,b]` with one on `[b,c]` that starts where the first ends. -/
theorem solutionExists_glue {f : ℝ → ℝ → ℝ} {y : ℝ} {x₁ x₂ : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : SolutionExists f y x₁ a b (Set.Icc a b))
    (h₂ : SolutionExists f (x₁ b) x₂ b c (Set.Icc b c)) :
    ∃ x : ℝ → ℝ, SolutionExists f y x a c (Set.Icc a c) := by
  classical
  refine ⟨fun s => if s ≤ b then x₁ s else x₂ s, ?_⟩
  set x : ℝ → ℝ := fun s => if s ≤ b then x₁ s else x₂ s with hxdef
  have hxle : ∀ s, s ≤ b → x s = x₁ s := by
    intro s hs; change (if s ≤ b then x₁ s else x₂ s) = x₁ s; exact ite_eq_left hs
  have hxgt : ∀ s, b < s → x s = x₂ s := by
    intro s hs; change (if s ≤ b then x₁ s else x₂ s) = x₂ s; exact ite_eq_right (not_le.mpr hs)
  have hxb : x b = x₁ b := hxle b le_rfl
  have hxIcc₁ : ∀ u ∈ Set.Icc a b, x u = x₁ u := fun u hu => hxle u hu.2
  have hxIcc₂ : ∀ u ∈ Set.Icc b c, x u = x₂ u := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h, hxb, h₂.1]
    · exact hxgt u h
  refine ⟨by rw [hxle a hab]; exact h₁.1, ?_⟩
  intro s hs
  rcases lt_trichotomy s b with hsb | hsb | hsb
  · -- s < b : use the left piece, then enlarge the set through `Iio b`
    have hmem₁ : s ∈ Set.Icc a b := ⟨hs.1, hsb.le⟩
    have hxs : x s = x₁ s := hxle s hsb.le
    have d : HasDerivWithinAt x (f s (x s)) (Set.Icc a b) s := by
      rw [hxs]; exact (h₁.2 s hmem₁).congr (fun u hu => hxIcc₁ u hu) hxs
    refine d.mono_of_mem_nhdsWithin ?_
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin (Set.Icc a c) (isOpen_Iio.mem_nhds hsb)) ?_
    rintro u ⟨hu1, hu2⟩
    exact ⟨hu1.1, le_of_lt hu2⟩
  · -- s = b : two one-sided derivatives, unioned
    subst hsb
    have d₁ : HasDerivWithinAt x (f s (x₁ s)) (Set.Icc a s) s :=
      (h₁.2 s ⟨hab, le_rfl⟩).congr (fun u hu => hxIcc₁ u hu) hxb
    have d₂ : HasDerivWithinAt x (f s (x₁ s)) (Set.Icc s c) s := by
      have h := h₂.2 s ⟨le_rfl, hbc⟩
      rw [h₂.1] at h
      exact h.congr (fun u hu => hxIcc₂ u hu) (hxIcc₂ s ⟨le_rfl, hbc⟩)
    have hu := d₁.union d₂
    rw [Set.Icc_union_Icc_eq_Icc hab hbc] at hu
    rw [hxb]
    exact hu
  · -- b < s : use the right piece, then enlarge the set through `Ioi b`
    have hmem₂ : s ∈ Set.Icc b c := ⟨hsb.le, hs.2⟩
    have hxs : x s = x₂ s := hxgt s hsb
    have d : HasDerivWithinAt x (f s (x s)) (Set.Icc b c) s := by
      rw [hxs]; exact (h₂.2 s hmem₂).congr (fun u hu => hxIcc₂ u hu) hxs
    refine d.mono_of_mem_nhdsWithin ?_
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin (Set.Icc a c) (isOpen_Ioi.mem_nhds hsb)) ?_
    rintro u ⟨hu1, hu2⟩
    exact ⟨le_of_lt hu2, hu1.2⟩

/-- Iterate the glue: `n` steps of size `τ` from any start time and any initial value. -/
theorem exists_solution_of_step {f : ℝ → ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hloc : ∀ a y : ℝ, ∃ x, SolutionExists f y x a (a + τ) (Set.Icc a (a + τ))) :
    ∀ (n : ℕ) (a y : ℝ), ∃ x, SolutionExists f y x a (a + n * τ) (Set.Icc a (a + n * τ)) := by
  intro n
  induction n with
  | zero =>
      intro a y
      obtain ⟨x, hx⟩ := hloc a y
      have h := hx.shrink (b' := a) (by linarith)
      use x
      grind
  | succ n ih =>
      intro a y
      obtain ⟨x₁, h₁⟩ := ih a y
      obtain ⟨x₂, h₂⟩ := hloc (a + (n : ℝ) * τ) (x₁ (a + (n : ℝ) * τ))
      have hnt : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ
      have hab : a ≤ a + (n : ℝ) * τ := by linarith
      have hbc : a + (n : ℝ) * τ ≤ a + (n : ℝ) * τ + τ := by linarith
      have heq : a + ((n : ℝ) + 1) * τ = a + (n : ℝ) * τ + τ := by ring
      push_cast
      rw [heq]
      exact solutionExists_glue hab hbc h₁ h₂

/-
The following theorem proves the existence of a solution to the initial value problem
`x' = f(t, x), x(0) = x0` on the interval [0, T] under the assumptions that f is continuous
and Lipschitz in its second argument with constant K. The proof uses induction on subintervals
of length t = 1/(2K) and applies the `Picard-Lindelöf` theorem on each subinterval to construct
a solution piecewise.
-/
theorem existence_by_induction (f : ℝ → ℝ → ℝ) (x0 : ℝ) (T : NNReal)
      (hKne : K ≠ 0)
      (hfc : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
      (hfl : ∀ t, LipschitzWith (K : NNReal) (fun x => f t x)) :
      ∃ x : ℝ → ℝ, SolutionExists f x0 x (0 : ℝ) T (Set.Icc (0 : ℝ) T) := by
      let t := 1/(2 * K)
      have htb : 0 < t := by positivity
      let N := Nat.ceil (T / t)
      have hloc : ∀ a y : ℝ, ∃ x, SolutionExists f y x a (a + t) (Set.Icc a (a + t)) := by
        intro a y
        have hfb : ∃ M : ℝ, ∀ s ∈ Set.Icc (a : ℝ) (a + t), |f s y| ≤ M := by
          let func := fun p : ℝ × ℝ => f p.1 p.2
          let g := fun p : ℝ => func (p, y)
          have hg : Continuous g := by
            apply Continuous.along_fst
            exact hfc
          have : ∃ M : ℝ, ∀ s ∈ Set.Icc (a : ℝ) (a + t), ‖g s‖ ≤ M := by
            apply IsCompact.exists_bound_of_continuousOn
            · exact isCompact_Icc
            · exact hg.continuousOn
          let ⟨M, hM⟩ := this
          use M
          intro s hs
          specialize hM s hs
          simp only [Real.norm_eq_abs] at hM
          exact hM
        let ⟨M, hM⟩ := hfb
        let M : NNReal :=
        ⟨M, by specialize hM a (by exact ⟨by grind, by simp only [le_add_iff_nonneg_right,
          NNReal.zero_le_coe]⟩); grind⟩
        let t₀ : Set.Icc (a : ℝ) (a + t) := ⟨a, by simp, by simp⟩
        have ipl : IsPicardLindelof f t₀ y (2*M/K) 0 (3*M) K := by
          constructor
          · intro s hs
            specialize hfl s
            apply LipschitzWith.lipschitzOnWith
            exact hfl
          · intro x hx
            let func := fun p : ℝ × ℝ => f p.1 p.2
            let g := fun p : ℝ => func (p, x)
            have hg : Continuous g := by
              apply Continuous.along_fst
              exact hfc
            have : (fun s => f s x) = g := by rfl
            rw [this]
            exact hg.continuousOn
          · intro s hs x hx
            have hlip : ‖f s x - f s y‖ ≤ (K : ℝ) * ‖x - y‖ := by
              specialize hfl s x y
              rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm] at hfl
              rw [← ENNReal.ofReal_coe_nnreal] at hfl
              rw [← ENNReal.ofReal_mul] at hfl
              · simp only at hfl
                · rw [ENNReal.ofReal_le_ofReal_iff] at hfl
                  · exact hfl
                  · apply mul_nonneg
                    · simp only [NNReal.zero_le_coe]
                    · exact norm_nonneg _
              · exact NNReal.coe_nonneg K
            have hM' : ‖f s x - f s y‖ ≤ 2 * M := by
              apply le_trans hlip
              calc
                (K : ℝ) * ‖x - y‖ ≤ (K : ℝ) * (2*M/K) := by
                  apply mul_le_mul_of_nonneg_left
                  · exact hx
                  · exact NNReal.coe_nonneg K
                _ = 2 * M := by field_simp
            calc
              ‖f s x‖ ≤ |‖f s x‖ - ‖f s y‖| + ‖f s y‖ := by grind only [=
                  abs.eq_1,
                = max_def]
              |‖f s x‖ - ‖f s y‖| + ‖f s y‖ ≤ ‖f s x - f s y‖ + ‖f s y‖
                          := by grind only [abs_norm_sub_norm_le]
              _ ≤ 2 * M + ‖f s y‖ := by linarith only [hM']
              _ ≤ 3 * M := by specialize hM s hs
                              simp only [Real.norm_eq_abs]
                              have : |f s y| ≤ M := hM
                              linarith
          · simp only [NNReal.coe_mul, NNReal.coe_ofNat, sub_zero, NNReal.coe_div,
            NNReal.coe_zero]
            have : t₀ = (a : ℝ) := by grind
            rw [this]
            simp only [add_sub_cancel_left, sub_self, NNReal.zero_le_coe, sup_of_le_left, ge_iff_le]
            calc
              _ = (3* M * 1/(2*K) : ℝ) := by simp only [t]; push_cast; ring
              _ = (3 * M / (2*K) : ℝ) := by ring
              _ = (3 / 2 : ℝ) * (↑M / ↑K) := by ring
              _ ≤ 2 * (↑M / ↑K) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
              _ = 2 * ↑M / ↑K := by ring
        let ⟨x, hxe⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ ipl
        use x
        constructor
        · grind
        · intro t ht
          grind
      let ⟨x, hxe⟩ := exists_solution_of_step (by linarith) hloc N 0 x0
      use x
      have hTR : (T : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
        change (T : ℝ) ≤ ((⌈T / t⌉₊ : ℕ) : ℝ) * (t : ℝ)
        have htpos : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr htb
        have h1 : ((T : ℝ) / (t : ℝ)) ≤ ((⌈T / t⌉₊ : ℕ) : ℝ) := by
          have h := NNReal.coe_le_coe.mpr (Nat.le_ceil (T / t))
          push_cast at h
          exact h
        field_simp at h1
        grind
      exact hxe.shrink (b' := T) (by linarith)

end ODE
