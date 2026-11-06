module

public import DynaLean.Defs
public import DynaLean.EulerScheme
public import DynaLean.EulerBound

@[expose] public section
#check Fin
namespace ODE
#check norm_image_sub_le_of_norm_deriv_le_segment'


def MemBox {k : ℕ} (x : ℝ^k) (A B : List (Option ℚ)) : Prop :=
  ∀ i : Fin k,
  match A[i]!, B[i]! with
  | some a, some b => (a ≤ x i) ∧ (x i ≤ b)
  | some a, none => a ≤ x i
  | none, some b => x i ≤ b
  | none, none => True

structure TimeVals (t₀ T : ℚ) where
  L : List ℚ
  hLne : L ≠ []
  hL : t₀ = L.head hLne ∧ ∀ t ∈ L, t₀ ≤ t ∧ t ≤ T

structure DigitalTwin {k : ℕ} (y z : ℝ → ℝ^k)
  (f g : ℝ → (ℝ^k) → ℝ^k) (x₀ : ℝ^k)
  (ε : ℝ) (t₀ T : ℚ) where
  L : TimeVals t₀ T
  hz : SolutionExistsVector g x₀ z (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T)
  hfg : ∀ (t : ℝ), t ∈ Set.Icc (t₀ : ℝ) T →  ‖f t (y t) - g t (z t)‖ ≤ ε

section MemBox
structure DigitalTwinBoxMem {k : ℕ} (y z : ℝ → ℝ^k) (f g : ℝ → (ℝ^k) → ℝ^k) (x₀ : ℝ^k)
  (ε : ℝ) (t₀ T : ℚ) extends DigitalTwin y z f g x₀ ε t₀ T where
  A : List (Option ℚ)
  B : List (Option ℚ)
  hA : A.length = k
  hB : B.length = k
  hmem : ∀ t ∈ L.L, MemBox (k := k) (z t) A B

theorem bound_twin {k : ℕ} (y : ℝ → ℝ^k) (t₀ T : ℚ) (x₀ : ℚ^k)
  (f g : ℝ → (ℝ^k) → ℝ^k)
  (hy : SolutionExistsVector f x₀ y (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T))
  (z : ℝ → ℝ^k) (ε : ℝ)
  (D : DigitalTwin y z f g x₀ ε t₀ T)
  : ∀ t ∈ Set.Icc (t₀ : ℝ) T, ‖y t - z t‖ ≤ ε * (t - (t₀ : ℝ)) := by
  intro t ht
  set q := fun t => y t - z t with hq
  have hq' : ∀ s ∈ Set.Icc (t₀ :ℝ) T,
    HasDerivWithinAt q (f s (y s) - g s (z s)) (Set.Icc (t₀ :ℝ) T) s := by
    intro s hs
    rw [hq]
    apply HasDerivWithinAt.sub (hy.2 s hs) (D.hz.2 s hs)
  change ‖q t‖ ≤ ε * (t - (t₀ : ℝ))
  have triv : q t = q t - q t₀ := by
    rw [hq]
    simp only
    rw [hy.1, D.hz.1]
    simp only [WithLp.equiv_symm_apply, sub_self, sub_zero]
  rw [triv]
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (f := q) (x := t) (b := (T : ℝ)) hq' _ ht
  intro s hs
  have hfg := D.hfg s (by grind)
  exact hfg

#search "Real.sqrt ((sqrtUB x) ^ 2) = sqrtUB x?"
def sqrtUB (x : ℚ) : ℚ := (Nat.sqrt (x.num.toNat * x.den) + 1) / x.den

theorem le_sq_sqrtUB (x : ℚ) (hx : 0 ≤ x) : x ≤ (sqrtUB x) ^ 2 := by
  simp only [sqrtUB]
  have h : x = (x.num.toNat * x.den) / (x.den * x.den) := by
    rw [← div_mul_div_comm]
    simp only [ne_eq, Nat.cast_eq_zero, Rat.den_ne_zero, not_false_eq_true, div_self, mul_one]
    have : 0 ≤ x.num := Rat.num_nonneg.mpr hx
    have hn : x.num.toNat = (x.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg this
    rw [hn]
    rw [Rat.num_div_den]
  field_simp [h]
  simp only [pow_two]
  apply le_trans (b := (x.num.toNat * x.den: ℚ))
  · apply Eq.le
    grind
  · norm_cast
    apply (Nat.lt_succ_sqrt (x.num.toNat * x.den)).le

theorem sqrt_le_sqrtUB (x : ℚ) (hx : 0 ≤ x) : Real.sqrt x ≤ (sqrtUB x : ℝ) := by
  have h : (x : ℝ) ≤ (sqrtUB x : ℝ) ^ 2 := by
    norm_cast
    apply le_sq_sqrtUB x hx
  have hsqrt : 0 ≤ (sqrtUB x : ℝ) := by
    norm_cast
    simp only [sqrtUB]
    positivity
  have h' : Real.sqrt ((sqrtUB x) ^ 2) = sqrtUB x := Real.sqrt_sq hsqrt
  rw [← h']
  apply Real.sqrt_le_sqrt h

def ObtainLU {k : ℕ} (c : ℚ^k) (r : ℚ) (A B : List (Option ℚ)) : List (ℚ × ℚ) :=
  List.ofFn fun i : Fin k =>
    ( match A[(i : ℕ)]! with | some a => max a (c.ofLp i - r) | none => c.ofLp i - r,
      match B[(i : ℕ)]! with | some b => min b (c.ofLp i + r) | none => c.ofLp i + r )


def Rec {k : ℕ} (c : ℚ^k) (r : ℚ) (A B : List (Option ℚ)) : Option ((ℚ^k) × ℚ) :=
  let LU := ObtainLU c r A B
  if LU.all (fun (l, u) => l ≤ u) then
    let rbox := sqrtUB ((LU.map (fun (l, u) => ((u - l) / 2) ^ 2)).sum)
    if rbox ≤ r then
      some ((WithLp.equiv 2 (Fin k → ℚ)).symm (fun i => (LU[i]!.1 + LU[i]!.2) / 2), rbox)
    else
      some (c, r)
  else
    none

lemma sum_fin_bang_eq_map_sum {α M : Type*} [AddCommMonoid M] [Inhabited α]
    {k : ℕ} (L : List α) (hk : L.length = k) (g : α → M) :
    (∑ i : Fin k, g L[i.val]!) = (L.map g).sum := by
  subst hk
  induction L with
  | nil =>
    simp
  | cons x xs ih =>
    have : (x :: xs).length = xs.length + 1 := by simp
    rw [this]
    rw [List.map_cons, List.sum_cons, Fin.sum_univ_succ
      (f := fun i : Fin (xs.length + 1)=> g (x :: xs)[(i : ℕ)]!)]
    have h_zero : (x :: xs)[(0 : Fin (xs.length + 1)).val]! = x := rfl
    have h_succ (i : Fin xs.length) : (x :: xs)[i.succ.val]! = xs[i.val]! := rfl
    simp_rw [h_zero, h_succ]
    rw [ih]

theorem rec_sound {k : ℕ} (c c' : ℚ^k) (r r' : ℚ) (A B : List (Option ℚ))
  (hrec : Rec c r A B = some (c', r')) (v : ℝ^k) (hv : MemBox v A B)
  (hr : ‖v - c‖ ≤ r) : ‖v - c'‖ ≤ r' := by
  simp only [Rec, List.all_eq_true, decide_eq_true_eq, Prod.forall, Fin.getElem!_fin,
  WithLp.equiv_symm_apply, Option.ite_none_right_eq_some] at hrec
  set hLU := ObtainLU c r A B with hLU_def
  have hk : k = hLU.length := by simp only [hLU_def, ObtainLU, List.length_ofFn]
  have hvi : ∀ i : Fin k, v i ∈ Set.Icc ((c : ℝ^k) i - r) (c i + r) := by
    intro i
    have hcoord := PiLp.norm_apply_le (v - (c : ℝ^k)) i
    have h_le := hcoord.trans hr
    rw [Real.norm_eq_abs] at h_le
    change |v i - c i| ≤ r at h_le
    rw [abs_le] at h_le
    simp only [WithLp.equiv_symm_apply, Set.mem_Icc]
    exact ⟨by linarith , by linarith⟩
  by_cases h : sqrtUB (List.map (fun x ↦ ((x.2 - x.1) / 2) ^ 2) hLU).sum ≤ r
  · simp only [h, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hrec
    have hab := hrec.1
    have hc := hrec.2.1
    have hr' := hrec.2.2
    have hvj : ∀ i : Fin k, (hLU[i]!.1 ≤ v i) ∧ (v i ≤ hLU[i]!.2) := by
      intro i
      have hmemi := hv i
      simp only [ObtainLU, List.length_ofFn, Fin.is_lt,
        getElem!_pos, Fin.getElem_fin, List.getElem_ofFn, Fin.eta, hLU]
      split
      · rename_i a hcasesa
        split
        · rename_i b hcasesb
          simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
          simp only [Rat.cast_max, Rat.cast_sub, sup_le_iff, tsub_le_iff_right, Rat.cast_min,
            Rat.cast_add, le_inf_iff]
          have hvi := hvi i
          simp only [WithLp.equiv_symm_apply, Set.mem_Icc, tsub_le_iff_right] at hvi
          apply And.intro (And.intro hmemi.1 hvi.1) (And.intro hmemi.2 hvi.2)
        · rename_i b hcasesb
          simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
          simp only [Rat.cast_max, Rat.cast_sub, sup_le_iff, tsub_le_iff_right,
            Rat.cast_add]
          have hvi := hvi i
          simp only [WithLp.equiv_symm_apply, Set.mem_Icc, tsub_le_iff_right] at hvi
          apply And.intro (And.intro hmemi hvi.1) hvi.2
      · rename_i a hcasesa
        split
        · rename_i b hcasesb
          simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
          simp only [Rat.cast_sub, tsub_le_iff_right, Rat.cast_min, Rat.cast_add, le_inf_iff]
          have hvi := hvi i
          simp only [WithLp.equiv_symm_apply, Set.mem_Icc, tsub_le_iff_right] at hvi
          apply And.intro hvi.1 (And.intro hmemi hvi.2)
        · rename_i b hcasesb
          simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
          simp only [Rat.cast_sub, tsub_le_iff_right, Rat.cast_add]
          have hvi := hvi i
          simp only [WithLp.equiv_symm_apply, Set.mem_Icc, tsub_le_iff_right] at hvi
          apply And.intro hvi.1 hvi.2
    simp only [WithLp.equiv_symm_apply, ge_iff_le]
    have hmidi : ∀ i : Fin k, |v i - (c' : ℝ^k) i| ≤ (hLU[i]!.2 - hLU[i]!.1) / 2 := by
      intro i
      have hmemi := hvj i
      rw [← hc]
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
        WithLp.equiv_symm_apply, Fin.getElem!_fin, ge_iff_le]
      rw [abs_le]
      constructor <;> grind
    rw [PiLp.norm_eq_of_L2]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs, ge_iff_le]
    simp only [WithLp.equiv_symm_apply, Fin.getElem!_fin] at hmidi
    have hsum : ∑ i, (v i - (c' i)) ^ 2 ≤ r'^2 := by
      have hsum' : ∑ i, (v i - (c' i)) ^ 2 ≤ ∑ i : Fin k, ((hLU[i]!.2 - hLU[i]!.1) / 2 : ℝ) ^ 2 :=
      by
        apply Finset.sum_le_sum
        intro i hi
        have hival : i < hLU.length := by rw [← hk]; exact i.2
        rw [sq_le_sq]
        rw [abs_of_nonneg (a := ((hLU[i]!.2 - hLU[i]!.1) / 2 : ℝ))]
        · exact hmidi i
        · field_simp
          simp only [zero_mul, Fin.getElem!_fin, sub_nonneg,
            Rat.cast_le]
          exact hab hLU[i]!.1 hLU[i]!.2
            (by simp only [Fin.getElem!_fin, Prod.mk.eta]
                rw [getElem!_pos]
                · exact List.getElem_mem hival)
      have hsum'' : ∑ i : Fin k, (((hLU[i]!.2 : ℝ) - hLU[i]!.1) / 2) ^ 2 ≤ (r' : ℝ)^2 := by
        apply le_trans (b := (hLU.map (fun x ↦ (((x.2 : ℝ) - x.1) / 2) ^ 2)).sum)
        · apply Eq.le
          set g := fun x : (ℚ × ℚ) => (((x.2 : ℝ) - x.1) / 2) ^ 2 with hg
          apply sum_fin_bang_eq_map_sum (g := g)
          exact hk.symm
        · apply (Real.sqrt_le_sqrt_iff (by positivity)).mp
          rw [hr'.symm]
          have : (hLU.map (fun x : ℚ × ℚ ↦ (((x.2 : ℝ) - x.1) / 2) ^ 2)).sum =
            ((hLU.map (fun x : ℚ × ℚ ↦ (((x.2  - x.1) / 2) ^ 2 : ℚ))).sum : ℝ) := by
               simp only [Rat.cast_list_sum, List.map_map]
               rw [List.sum]
               apply List.Perm.sum_eq
               set fR := fun (x : ℚ × ℚ) ↦ (((x.2 : ℝ) - (x.1 : ℝ)) / 2) ^ 2 with hfR
               set Rf := Rat.cast (K := ℝ) ∘ fun (x : ℚ × ℚ) ↦ ((x.2 - x.1) / 2) ^ 2 with hRf
               have : fR = Rf := by
                 funext x
                 simp only [hfR, hRf]
                 simp only [Function.comp_apply, Rat.cast_pow, Rat.cast_div, Rat.cast_sub,
                   Rat.cast_ofNat]
               rw [this]
          rw [this]
          rw [Real.sqrt_sq (by
              apply le_trans (a := (0 : ℝ))
                (b := Real.sqrt (List.map (fun x : ℚ × ℚ ↦ (((x.2 - x.1) / 2) ^ 2 : ℚ)) hLU).sum)
              · simp only [Rat.cast_list_sum, List.map_map, Real.sqrt_nonneg]
              · apply sqrt_le_sqrtUB
                apply List.sum_nonneg
                intro x hx
                simp only [List.mem_map] at hx
                let ⟨a, hx⟩ := hx
                rw [hx.2.symm]
                apply sq_nonneg
                )]
          apply sqrt_le_sqrtUB
          apply List.sum_nonneg
          intro x hx
          simp only [List.mem_map] at hx
          let ⟨a, hx⟩ := hx
          rw [hx.2.symm]
          apply sq_nonneg
      exact le_trans hsum' hsum''
    rw [← Real.sqrt_sq (x := r')]
    · apply Real.sqrt_le_sqrt hsum
    · apply le_trans (a := (0 : ℝ))
       (b := Real.sqrt (List.map (fun x : ℚ × ℚ ↦ (((x.2 - x.1) / 2) ^ 2 : ℚ)) hLU).sum)
      · simp only [Rat.cast_list_sum, List.map_map, Real.sqrt_nonneg]
      · rw [hr'.symm]
        apply sqrt_le_sqrtUB
        apply List.sum_nonneg
        intro x hx
        simp only [List.mem_map] at hx
        let ⟨a, hx⟩ := hx
        rw [hx.2.symm]
        apply sq_nonneg
  · simp only [h, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hrec
    rw [hrec.2.1.symm, hrec.2.2.symm]
    exact hr


theorem rec_refute {k : ℕ} (c : ℚ^k) (r : ℚ) (A B : List (Option ℚ))
  (hrec : Rec c r A B = none) (v : ℝ^k) (hv : MemBox v A B)
  (hr : ‖v - c‖ ≤ r) : False := by
  simp only [Rec, List.all_eq_true, decide_eq_true_eq, Prod.forall, Fin.getElem!_fin,
    List.getElem!_eq_getElem?_getD, WithLp.equiv_symm_apply, ite_eq_right_iff] at hrec
  let hLU := ObtainLU c r A B
  have claim : ¬ (∀ (a b : ℚ), (a, b) ∈ hLU → a ≤ b) := by
    by_contra
    have h := hrec this
    grind
  simp only [not_forall, not_le] at claim
  let ⟨a, b, hclaim1, hclaim2⟩ := claim
  simp only [ObtainLU, List.mem_ofFn, Prod.mk.injEq, hLU] at hclaim1
  let ⟨i, hi⟩ := hclaim1
  have hvineq : c i - r ≤ v i ∧ v i ≤ c i + r := by
    have hcoord := PiLp.norm_apply_le (v - (c : ℝ^k)) i
    have h_le := hcoord.trans hr
    rw [Real.norm_eq_abs] at h_le
    change |v i - c i| ≤ r at h_le
    rw [abs_le] at h_le
    simp only
    exact ⟨by linarith , by linarith⟩
  have triv : c i - r ≤ (c i + r : ℝ) := by
    simp only [tsub_le_iff_right]
    rw [add_assoc]
    simp only [le_add_iff_nonneg_right, nonneg_add_self_iff]
    apply le_trans _ hr
    grind
  have habR : (b : ℝ) < a := by exact_mod_cast hclaim2
  match hcasesa : A[(i : ℕ)]!, hcasesb : B[(i : ℕ)]! with
  | some a', some b' =>
    simp only [hcasesa, hcasesb] at hi
    have hmemi := hv i
    simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
    by_cases h1 : a' ≤ c i - r
    · simp only [h1, sup_of_le_right] at hi
      by_cases h2 : c i + r ≤ b'
      · simp only [h2, inf_of_le_right] at hi
        rw [hi.1.symm, hi.2.symm] at habR
        push_cast at habR
        grind
      · simp only [not_le] at h2
        have h2' := h2.le
        simp only [h2', inf_of_le_left] at hi
        have h4 : (b' : ℝ) < c i - r := by norm_cast; grind
        grind
    · simp only [not_le] at h1
      have h1' := h1.le
      simp only [h1', sup_of_le_left] at hi
      by_cases h2 : c i + r ≤ b'
      · simp only [h2, inf_of_le_right] at hi
        have h3 : (c i + r : ℝ) < a' := by norm_cast; grind
        grind
      · simp only [not_le] at h2
        have h2' := h2.le
        simp only [h2', inf_of_le_left] at hi
        have h4 : (b' : ℝ) < c i - r := by norm_cast; grind
        grind
  | some a', none =>
    simp only [hcasesa, hcasesb] at hi
    have hmemi := hv i
    simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
    by_cases h1 : a' ≤ c i - r
    · simp only [h1, sup_of_le_right] at hi
      norm_cast at triv
      grind
    · simp only [not_le] at h1
      have h1' := h1.le
      simp only [h1', sup_of_le_left] at hi
      have h3 : (c i + r : ℝ) < a' := by norm_cast; grind
      grind
  | none, some b' =>
    simp only [hcasesa, hcasesb] at hi
    have hmemi := hv i
    simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
    by_cases h2 : c i + r ≤ b'
    · simp only [h2, inf_of_le_right] at hi
      norm_cast at triv
      grind
    · simp only [not_le] at h2
      have h2' := h2.le
      simp only [h2', inf_of_le_left] at hi
      have h4 : (b' : ℝ) < c i - r := by norm_cast; grind
      grind
  | none, none =>
    simp only [hcasesa, hcasesb] at hi
    have hmemi := hv i
    simp only [Fin.getElem!_fin, hcasesa, hcasesb] at hmemi
    norm_cast at triv
    grind



end MemBox
end ODE
