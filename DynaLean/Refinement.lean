import Mathlib
import DynaLean.Defs
import DynaLean.EulerScheme
import DynaLean.EulerBound

/-!-/
namespace ODE
def Rule (S : Set ℝ) (x : ℝ → ℝ) (t₀ T : ℝ) := ∀ t ∈ Set.Icc t₀ T, x t ∈ S

abbrev bound := Option ℚ

def BdAbv (y : ℝ) (b : bound) : Prop :=
  match b with
  | none => True
  | some b => y ≤ b

def BdBlw (y : ℝ) (b : bound) : Prop :=
  match b with
  | none => True
  | some b => y ≥ b

def BdAbvF (x : ℝ → ℝ) (t₀ T : ℝ) (b : bound) : Prop := ∀ t ∈ Set.Icc t₀ T, BdAbv (x t) b

def BdBlwF (x : ℝ → ℝ) (t₀ T : ℝ) (b : bound) : Prop := ∀ t ∈ Set.Icc t₀ T, BdBlw (x t) b


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


def egScheme : Scheme := {
  t₀ := 0
  x₀ := 1
  δ := 1
  m := fun t y => y
  hδ := by grind
}

#eval refinement egScheme 1 1 1 0 5 (some 0) (some 2) 3 (by simp only [sub_zero, egScheme, div_one,
  Nat.floor_ofNat, Nat.reduceAdd, Finset.mem_range, Nat.reduceLT])
end ODE
