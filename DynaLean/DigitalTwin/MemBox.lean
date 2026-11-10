module

public import DynaLean.Defs
public import DynaLean.EulerScheme
public import DynaLean.EulerBound
public import DynaLean.DigitalTwin.Defs

@[expose] public section

/-! # Digital twins: soundness of the tube construction

`DynaLean.DigitalTwin.Defs` defines the computation: `ODE.Rec` re-centres a ball on a
measurement, `ODE.segEnd` pushes it across a segment, `ODE.nodeAt` alternates the two,
and `ODE.BuildTube` runs the whole schedule. This module proves that the computation
means what it should.

The results, in dependency order:

* **Rational square roots.** `ODE.le_sq_sqrtUB`, `ODE.sqrt_le_sqrtUB` and
  `ODE.norm_le_qnormUB` establish that `ODE.sqrtUB` really over-approximates `√`, which
  is what keeps the exactly-rational radius arithmetic sound.
* **Re-centring.** `ODE.rec_sound` — if a state is in the old ball and in the measured
  box, it is in the ball `Rec` returns. `ODE.rec_refute` — if `Rec` returns `none`, no
  such state exists.
* **Twin drift.** `ODE.bound_twin_shift` and `ODE.bound_twin` bound the separation of
  two trajectories whose velocities differ by at most `ε`: it grows at most linearly,
  `‖w t - z t‖ ≤ ‖w τ - z τ‖ + ε (t - τ)`.
* **Segments.** `ODE.segment_estimate`, `ODE.segment_estimate_grid` and
  `ODE.segment_estimate_at` combine twin drift with the Euler bound by the triangle
  inequality: true trajectory → model solution → interpolant.
* **The main theorems.** `ODE.node_invariant` (the twin is inside the computed ball at
  every node), `ODE.tube_enclosure` and `ODE.tube_enclosure_global` (it is inside the
  tube at *every* time), and `ODE.drift_sound` (if `BuildTube` returns `none`, no twin
  consistent with the measurements exists at all).

`ODE.drift_sound` is the practically interesting direction: a failed computation is a
*proof* that the model has drifted out of its stated error budget, not merely a
failure to establish containment.
-/

namespace ODE



section MemBox

/-- Every measurement time of a schedule lies in `[t₀, T]`.

Immediate from strict monotonicity of `τ` together with `τ 0 = t₀` and
`τ (last p) = T`; used constantly to transfer hypotheses stated on `[t₀, T]` to a
single segment. -/
theorem time_mem_schedule {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (i : Fin (sch.p + 1)) :
  (sch.τ i : ℝ) ∈ Set.Icc (t₀ : ℝ) T := by
  apply Set.mem_Icc.mpr
  constructor
  · norm_cast
    simp only [← sch.hfirst]
    apply sch.hmono.monotone
    grind
  · norm_cast
    simp only [← sch.hlast]
    apply sch.hmono.monotone
    grind

end MemBox

/-! ## `sqrtUB` really is an upper bound for the square root -/

/-- `ODE.sqrtUB` squares to at least `x`: `x ≤ (sqrtUB x) ^ 2` for `0 ≤ x`.

Writing `x = p / q` with `p = x.num ≥ 0` and `q = x.den`, the claim reduces to
`p · q < (⌊√(p·q)⌋ + 1) ^ 2`, which is `Nat.lt_succ_sqrt`. -/
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

/-- `Real.sqrt x ≤ sqrtUB x` for `0 ≤ x`: the rational over-approximation dominates the
real square root.

The form in which `ODE.le_sq_sqrtUB` is actually used, since the quantities being
bounded (norms, radii) live in `ℝ`. -/
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

/-- `ODE.qnormUB` over-approximates the Euclidean norm: `‖x‖ ≤ qnormUB x`.

`ODE.sqrt_le_sqrtUB` applied to the sum of squares, after identifying the `L²` norm on
`ℝ^k` with `√(∑ xᵢ²)`. -/
theorem norm_le_qnormUB {k : ℕ} (x : ℚ^k) : ‖(x : ℝ^k)‖ ≤ (qnormUB x : ℝ) := by
  simp only [qnormUB]
  simp only [WithLp.equiv_symm_apply]
  rw [PiLp.norm_eq_of_L2]
  apply le_trans _ (sqrt_le_sqrtUB (∑ i : Fin k, (x i) ^ 2) _)
  · apply Real.sqrt_le_sqrt
    push_cast
    apply Eq.le
    set f : Fin k → ℝ := fun i => (x i) ^ 2 with hf
    set g : Fin k → ℝ := fun i => ‖(x i : ℝ)‖ ^ 2 with hg
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hf, hg, Real.norm_eq_abs, sq_abs]
  · apply Finset.sum_nonneg
    intro i hi
    simp only [sq_nonneg]

/-- Summing `g` over the indices of a list via `Fin`-indexed `getElem!` is the same as
summing `List.map g` over the list.

A plumbing lemma: `ODE.ObtainLU` returns a `List`, `ODE.Rec` sums over it with
`List.map`, but the enclosure proofs index coordinates by `Fin k`. This reconciles the
two views. -/
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

/-! ## Soundness of the re-centring step -/

/-- Re-centring preserves enclosure: if `Rec c r A B = some (c', r')`, then any state
in `closedBall c r` that also satisfies the box constraints lies in `closedBall c' r'`.

The two branches of `Rec` are checked separately: when the box is kept, `r'` is its
circumradius and the bound comes from `ODE.sqrtUB` over-approximating the diagonal;
when the prior ball is kept, the claim is the hypothesis itself. -/
theorem rec_sound {k : ℕ} {c c' : ℚ^k} {r r' : ℚ} {A B : Fin k → (Option ℚ)}
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
          simp only [hcasesa, hcasesb] at hmemi
          simp only [Rat.cast_max, Rat.cast_sub, sup_le_iff, tsub_le_iff_right, Rat.cast_min,
            Rat.cast_add, le_inf_iff]
          have hvi := hvi i
          simp only [WithLp.equiv_symm_apply, Set.mem_Icc, tsub_le_iff_right] at hvi
          apply And.intro (And.intro hmemi.1 hvi.1) (And.intro hmemi.2 hvi.2)
        · rename_i b hcasesb
          simp only [hcasesa, hcasesb] at hmemi
          simp only [Rat.cast_max, Rat.cast_sub, sup_le_iff, tsub_le_iff_right,
            Rat.cast_add]
          have hvi := hvi i
          simp only [WithLp.equiv_symm_apply, Set.mem_Icc, tsub_le_iff_right] at hvi
          apply And.intro (And.intro hmemi hvi.1) hvi.2
      · rename_i a hcasesa
        split
        · rename_i b hcasesb
          simp only [hcasesa, hcasesb] at hmemi
          simp only [Rat.cast_sub, tsub_le_iff_right, Rat.cast_min, Rat.cast_add, le_inf_iff]
          have hvi := hvi i
          simp only [WithLp.equiv_symm_apply, Set.mem_Icc, tsub_le_iff_right] at hvi
          apply And.intro hvi.1 (And.intro hmemi hvi.2)
        · rename_i b hcasesb
          simp only [hcasesa, hcasesb] at hmemi
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


/-- Failure of re-centring is a refutation: if `Rec c r A B = none`, no state at all
lies in `closedBall c r` and satisfies the box constraints.

`Rec` returns `none` only when some coordinate's clipped interval is empty, and a state
meeting both constraints would have to lie in it. This is the local step behind
`ODE.drift_sound`. -/
theorem rec_refute {k : ℕ} {c : ℚ^k} {r : ℚ} {A B : Fin k → (Option ℚ)}
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
  match hcasesa : A i, hcasesb : B i with
  | some a', some b' =>
    simp only [hcasesa, hcasesb] at hi
    have hmemi := hv i
    simp only [hcasesa, hcasesb] at hmemi
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
    simp only [hcasesa, hcasesb] at hmemi
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
    simp only [hcasesa, hcasesb] at hmemi
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
    simp only [hcasesa, hcasesb] at hmemi
    norm_cast at triv
    grind

/-! ## How fast two trajectories can separate -/

/-- Two trajectories whose velocities differ by at most `ε` separate at most linearly:
`‖w t - z t‖ ≤ ‖w τ - z τ‖ + ε (t - τ)` on `[τ, σ]`.

No Lipschitz hypothesis is needed, and no relation between `f` and `g` away from the
two trajectories: the difference `w - z` has derivative `f s (w s) - g s (z s)`, which
is bounded by `ε` by assumption, so the segment mean-value inequality applies directly.

This is what charges `εz · (t - τ)` of drift to the tube radius in `ODE.segRadius`. -/
theorem bound_twin_shift {k : ℕ} (w z : ℝ → ℝ^k) (f g : ℝ → (ℝ^k) → ℝ^k)
    (τ σ : ℝ) (ε : ℝ)
    (hw : ∀ s ∈ Set.Icc τ σ, HasDerivWithinAt w (f s (w s)) (Set.Icc τ σ) s)
    (hz : ∀ s ∈ Set.Icc τ σ, HasDerivWithinAt z (g s (z s)) (Set.Icc τ σ) s)
    (hfg : ∀ s ∈ Set.Icc τ σ, ‖f s (w s) - g s (z s)‖ ≤ ε) :
    ∀ t ∈ Set.Icc τ σ, ‖w t - z t‖ ≤ ‖w τ - z τ‖ + ε * (t - τ) := by
  intro t ht
  set q := fun t => w t - z t with hq
  have hq' : ∀ s ∈ Set.Icc τ σ,
    HasDerivWithinAt q (f s (w s) - g s (z s)) (Set.Icc τ σ) s := by
    intro s hs
    rw [hq]
    apply HasDerivWithinAt.sub (hw s hs) (hz s hs)
  change ‖q t‖ ≤ ‖q τ‖ + ε * (t - τ)
  have triv : q t = q t - q τ + q τ := by
    rw [hq]
    simp only [sub_add_cancel]
  rw [triv]
  apply le_trans (norm_add_le (a := q t - q τ) (b := q τ))
  rw [add_comm]
  simp only [add_le_add_iff_left]
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (f := q) (x := t) (b := σ) hq' _ ht
  intro s hs
  have hfg := hfg s (by grind)
  exact hfg

/-- `ODE.bound_twin_shift` for two trajectories sharing an initial value: then the
separation is purely drift, `‖w t - z t‖ ≤ ε (t - t₀)`. -/
theorem bound_twin {k : ℕ} (w z : ℝ → ℝ^k) (f g : ℝ → (ℝ^k) → ℝ^k)
    (t₀ T : ℚ) (ε : ℝ) (z₀ : ℝ^k)
    (hz : SolutionExistsVector g z₀ z (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T))
    (hw : SolutionExistsVector f z₀ w (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T))
    (hfg : ∀ t ∈ Set.Icc (t₀ : ℝ) T, ‖f t (w t) - g t (z t)‖ ≤ ε) :
    ∀ t ∈ Set.Icc (t₀ : ℝ) T, ‖w t - z t‖ ≤ ε * (t - t₀) := by
  intro t ht
  have hfg := bound_twin_shift w z f g (t₀ : ℝ) (T : ℝ) ε hw.2 hz.2 hfg t ht
  rw [hw.1, hz.1] at hfg
  simp only [sub_self, norm_zero, zero_add] at hfg
  exact hfg

/-- Zero Euler steps cost nothing: `EB K ε M δ 0 = 0`. -/
lemma EB_zero {K ε M δ : ℚ} : EB K ε M δ 0 = 0 := by
  simp only [EB]
  ring

/-- The Euler budget is monotone in the number of steps: more steps never shrink it.

Lets a bound established at one step index be reused at any later one. -/
lemma EB_mono {K ε M δ : ℚ} (hK : 0 < K) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hδ : 0 < δ) :
  Monotone (EB K ε M δ) := by
  intro s t hst
  simp only [EB]
  gcongr
  simp only [le_add_iff_nonneg_right]
  positivity

/-! ## Segment estimates

The three statements below are the same triangle inequality at three levels of
packaging. Write `z` for the true trajectory, `yc` for the exact solution of the model
field started at the node centre, and `C` for the computed curve (the Euler
interpolant). Then

`‖z - C‖ ≤ ‖z - yc‖ + ‖yc - C‖ ≤ (ρ + εz (t - τ)) + EB`,

where the first summand is bounded by `ODE.bound_twin_shift` and the second is the
Euler bound supplied by the caller. -/

/-- Enclosure on one segment, in its most general form: `C` is an arbitrary curve
tracking the model solution `yc` to within `EB t`, and the conclusion is
`‖z t - C t‖ ≤ ρ + εz (t - τ) + EB t`. -/
theorem segment_estimate {k : ℕ}
    {f g : ℝ → (ℝ^k) → ℝ^k} {z yc : ℝ → ℝ^k} (C : ℝ → ℝ^k)
    {ρ εz : ℝ} {EB : ℝ → ℝ} {τ σ : ℝ}
    (hyc : ∀ s ∈ Set.Icc (τ : ℝ) σ, HasDerivWithinAt yc (f s (yc s)) (Set.Icc (τ : ℝ) σ) s)
    (hz : ∀ s ∈ Set.Icc (τ : ℝ) σ, HasDerivWithinAt z (g s (z s)) (Set.Icc (τ : ℝ) σ) s)
    (hfg : ∀ s ∈ Set.Icc (τ : ℝ) σ, ‖f s (yc s) - g s (z s)‖ ≤ εz)
    (hρ : ‖z τ - yc τ‖ ≤ ρ)
    (hEB : ∀ t ∈ Set.Icc τ σ, ‖yc t - C t‖ ≤ EB t) :
    ∀ t ∈ Set.Icc τ σ, ‖z t - C t‖ ≤ ρ + εz * (t - τ) + EB t := by
  intro t ht
  have htri : ‖z t - C t‖ ≤ ‖z t - yc t‖ + ‖yc t - C t‖ := by
    have h := norm_add_le (z t - yc t) (yc t - C t)
    rwa [sub_add_sub_cancel] at h
  have htwin : ‖z t - yc t‖ ≤ ρ + εz * (t - τ) := by
    rw [norm_sub_rev]
    refine (bound_twin_shift yc z f g τ σ εz hyc hz hfg t ht).trans ?_
    gcongr
    rwa [norm_sub_rev]
  linarith [hEB t ht]

/-- `ODE.segment_estimate` specialized to the grid points of a concrete segment scheme.

Here `C` is the interpolant of `ODE.LastVectorSchema τ σ c m N` and the budget is the
rational `ODE.EB`, so the conclusion is a statement about computable quantities:
`‖z (τ + n δ) - S.pl (τ + n δ)‖ ≤ ρ + εz (n δ) + EB K M εm δ n` for every `n ≤ N`. -/
theorem segment_estimate_grid {k : ℕ}
    (f g : ℝ → (ℝ^k) → ℝ^k) (m : ℚ → (ℚ^k) → ℚ^k) (z yc : ℝ → ℝ^k)
    (τ σ : ℚ) (hτσ : τ < σ) (c : ℚ^k) (ρ εz εm K M : ℚ)
    (N : ℕ) (hN : N ≠ 0)
    (S : VectorScheme k) (hS : S = LastVectorSchema τ σ c m N hN hτσ)
    (hyc : SolutionExistsVector f (c : ℝ^k) yc (τ : ℝ) (σ : ℝ) (Set.Icc (τ : ℝ) (σ : ℝ)))
    (hz : ∀ s ∈ Set.Icc (τ : ℝ) (σ : ℝ),
             HasDerivWithinAt z (g s (z s)) (Set.Icc (τ : ℝ) (σ : ℝ)) s)
    (hfg : ∀ s ∈ Set.Icc (τ : ℝ) (σ : ℝ), ‖f s (yc s) - g s (z s)‖ ≤ (εz : ℝ))
    (hρ : ‖z τ - (c : ℝ^k)‖ ≤ (ρ : ℝ))
    (hEB : ∀ n : ℕ, n ≤ N →
             ‖yc (τ + n * S.δ) - S.pl (τ + n * S.δ)‖ ≤ (EB K M εm S.δ n : ℝ)) :
    ∀ n : ℕ, n ≤ N →
      ‖z (τ + n * S.δ) - S.pl (τ + n * S.δ)‖
        ≤ (ρ : ℝ) + (εz : ℝ) * (n * S.δ) + (EB K M εm S.δ n : ℝ) := by
  intro n hn
  have hδR : (S.δ : ℝ) > 0 := by exact_mod_cast S.hδ
  have htmem : (τ + n * S.δ : ℝ) ∈ Set.Icc (τ : ℝ) (σ : ℝ) := by
    simp only [Set.mem_Icc]
    apply And.intro (by simp only [le_add_iff_nonneg_right]; positivity)
    simp [hS, LastVectorSchema]
    field_simp
    norm_cast
    apply add_le_of_le_sub_left
    rw [← sub_mul, mul_comm]
    gcongr
  have h := norm_add_le (z (τ + n * S.δ) - yc (τ + n * S.δ)) (yc (τ + n * S.δ) - S.pl (τ + n * S.δ))
  rw [sub_add_sub_cancel] at h
  apply le_trans h
  have hEBn := hEB n hn
  gcongr
  have hb := bound_twin_shift yc z f g (τ : ℝ) (σ : ℝ) (εz : ℝ) hyc.2 hz hfg (τ + n * S.δ) htmem
  rw [norm_sub_rev, add_sub_cancel_left] at hb
  rw [norm_sub_rev, hyc.1.symm] at hρ
  grind

/-! ## Unfolding lemmas for `nodeAt` -/

/-- The first node is the prior ball re-centred on the first measurement. -/
@[simp] theorem nodeAt_zero {sch : Schedule k t₀ T} {εz εm : ℚ} :
    nodeAt sch m x₀ ρ₀ εz εm K M 0 = Rec x₀ ρ₀ (sch.A 0) (sch.B 0) :=
  Fin.induction_zero _ _

/-- Each later node is the previous one pushed across a segment (`ODE.segEnd`) and then
re-centred on the next measurement (`ODE.Rec`), with `Option.bind` short-circuiting a
run that has already been refuted. -/
@[simp] theorem nodeAt_succ {sch : Schedule k t₀ T} {εz εm : ℚ} (i : Fin sch.p) :
    nodeAt sch m x₀ ρ₀ εz εm K M i.succ
      = (nodeAt sch m x₀ ρ₀ εz εm K M i.castSucc).bind (fun p =>
          let (cE, rE) := segEnd sch m εz εm K M i p.1 p.2
          Rec cE rE (sch.A i.succ) (sch.B i.succ)) :=
  Fin.induction_succ _ _ _

/-- A successful node implies its predecessor succeeded: failure is absorbing, so
`nodeAt` can only be `some` at `i.succ` if it was `some` at `i.castSucc`. -/
theorem nodeAt_isSome_castSucc {sch : Schedule k t₀ T} {εz εm : ℚ}
    {i : Fin sch.p}
    (h : (nodeAt sch m x₀ ρ₀ εz εm K M i.succ).isSome) :
    (nodeAt sch m x₀ ρ₀ εz εm K M i.castSucc).isSome := by
  simp only [nodeAt_succ] at h
  by_contra hcast
  simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hcast
  simp only [hcast, Option.bind_none, Option.isSome_none, Bool.false_eq_true] at h

/-- `ODE.segment_estimate` at a single time, with the Euler bound supplied pointwise.

The form the main theorems actually use: instead of a curve `C` and a budget function,
it takes one point `Ct` and one number `EBt` with `‖yc t - Ct‖ ≤ EBt`, which is exactly
what a `ODE.SegmentCert` hands over. -/
theorem segment_estimate_at {k : ℕ}
    {f g : ℝ → (ℝ^k) → ℝ^k} {z yc : ℝ → ℝ^k} {τ σ : ℚ} {ρ εz : ℝ}
    (hyc : ∀ s ∈ Set.Icc (τ : ℝ) σ, HasDerivWithinAt yc (f s (yc s)) (Set.Icc (τ : ℝ) σ) s)
    (hz : ∀ s ∈ Set.Icc (τ : ℝ) σ, HasDerivWithinAt z (g s (z s)) (Set.Icc (τ : ℝ) σ) s)
    (hfg : ∀ s ∈ Set.Icc (τ : ℝ) σ, ‖f s (yc s) - g s (z s)‖ ≤ εz)
    (hρ : ‖z τ - yc τ‖ ≤ ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (τ : ℝ) σ) {Ct : ℝ^k} {EBt : ℝ} (hEB : ‖yc t - Ct‖ ≤ EBt) :
    ‖z t - Ct‖ ≤ ρ + εz * (t - τ) + EBt := by
  have h := norm_add_le (z t - yc t) (yc t - Ct)
  rw [sub_add_sub_cancel] at h
  apply le_trans h
  have hB := bound_twin_shift yc z f g (τ : ℝ) (σ : ℝ) εz hyc hz hfg t ht
  rw [norm_sub_rev] at hρ
  gcongr
  rw [norm_sub_rev]
  grind

/-! ## Main soundness theorems -/

/-- Node invariant: the twin is inside the recentred ball at every measurement node.

If the run succeeds at every node (`hrun`), every segment has a certificate (`hseg`),
`z` is a digital twin of `f` consistent with the measurements, and the prior
`‖z t₀ - x₀‖ ≤ ρ₀` holds, then `‖z (τ i) - (W i).1‖ ≤ (W i).2` for every node `i`.

By induction along the schedule. The base case is `ODE.rec_sound` applied to the prior;
the inductive step composes `ODE.segment_estimate_at` (carry the enclosure across the
segment, paying drift plus Euler error) with `ODE.rec_sound` (tighten it with the next
measurement). -/
theorem node_invariant {k : ℕ} {t₀ T : ℚ}
    (sch : Schedule k t₀ T) {f g : ℝ → (ℝ^k) → ℝ^k} {m : ℚ → (ℚ^k) → ℚ^k}
    {Ω : Set (ℝ × ℝ^k)} {εz εm K M : ℚ} {x₀ : ℚ^k} {ρ₀ : ℚ}
    {W : Fin (sch.p + 1) → Node k}
    (hrun : ∀ i, nodeAt sch m x₀ ρ₀ εz εm K M i = some (W i))
    (hseg : ∀ (i : Fin sch.p) (c : ℚ^k), SegmentCert sch f m Ω εm K M i c)
    {z : ℝ → ℝ^k} (D : DigitalTwin z f g Ω εz t₀ T)
    (hmeas : MeasuredBy z sch)
    (hprior : ‖z (t₀ : ℝ) - (x₀ : ℝ^k)‖ ≤ (ρ₀ : ℝ)) :
    ∀ i : Fin (sch.p + 1), ‖z (sch.τ i : ℝ) - (((W i).1 : ℚ^k) : ℝ^k)‖ ≤ (((W i).2 : ℚ) : ℝ)
    := Fin.induction
    (motive := fun i => ‖z (sch.τ i : ℝ) - (((W i).1 : ℚ^k) : ℝ^k)‖ ≤ (((W i).2 : ℚ) : ℝ))
    (by
    have h0 := hrun 0
    simp only [nodeAt_zero] at h0
    have h := rec_sound h0 (z (sch.τ 0 : ℝ))
                           (hmeas 0) (by rw [sch.hfirst]; exact hprior)
    exact h)
    (by
    intro i hi
    have h1 := hrun i.succ
    simp only [nodeAt_succ] at h1
    have h2 := hrun i.castSucc
    simp only [h2, Option.bind_some] at h1
    have hssub : Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ) ⊆ Set.Icc (t₀ : ℝ) (T : ℝ) := by
      intro t ht
      apply And.intro
      · apply le_trans _ ht.1
        exact (time_mem_schedule sch i.castSucc).1
      · apply le_trans ht.2 _
        exact (time_mem_schedule sch i.succ).2
    have hzsub : ∀ t ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ),
      HasDerivWithinAt z (g t (z t)) (Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ)) t := by
      intro t ht
      have h := D.hz.2 t (by grind)
      exact h.mono hssub
    let hsege := hseg i (W i.castSucc).1
    have hs := segment_estimate_at (hseg i (W i.castSucc).1).hy.2 hzsub (ρ := (W i.castSucc).2)
           (fun s hs => D.hfg s (by grind) (hsege.y s)
            (hsege.hyΩ s hs)) (by rw [hsege.hy.1]; exact hi) (t := (sch.τ i.succ : ℝ))
            (by simp only [Set.mem_Icc, Rat.cast_le, Std.le_refl, and_true]
                apply le_of_lt
                apply sch.hmono
                grind)
            (EBt := EB K εm M (sch.δ i) (sch.N i))
            (Ct := (LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) (W i.castSucc).1 m (sch.N i)
                (sch.hN i)
                (sch.hmono (Fin.castSucc_lt_succ))).x (sch.N i))
            (by
                have hEB := (hseg i (W i.castSucc).1).hEB (sch.τ i.succ : ℝ)
                  (Set.right_mem_Icc.mpr (by exact_mod_cast (sch.hmono (Fin.castSucc_lt_succ)).le))
                set S := LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) (W i.castSucc).1 m
                    (sch.N i)
                    (sch.hN i)
                    (sch.hmono (Fin.castSucc_lt_succ)) with hS
                have : sch.τ i.succ = S.t (sch.N i) := by
                  simp only [VectorScheme.t, hS, LastVectorSchema]
                  rw [IsUnit.mul_div_cancel _ (sch.τ i.succ - sch.τ i.castSucc)]
                  · simp only [add_sub_cancel]
                  · simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, sch.hN,
                    not_false_eq_true]
                simp only at hEB
                rw [this] at hEB
                rw [VectorScheme.plR_grid] at hEB
                rw [← this] at hEB
                exact hEB)
    have hmsucc := hmeas i.succ
    have hrec := rec_sound h1 (z (sch.τ i.succ : ℝ))
      (hmsucc) (by simp only [segEnd, Schedule.h, Rat.cast_add, Rat.cast_mul]
                   set S := LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) (W i.castSucc).1 m
                    (sch.N i)
                       (sch.hN i)
                       (sch.hmono (Fin.castSucc_lt_succ)) with hS
                   push_cast
                   simp only [WithLp.equiv_symm_apply, ge_iff_le]
                   simp only [WithLp.equiv_symm_apply] at hs
                   grind)
    exact hrec)

/-- The twin stays in the tube throughout each segment, not just at its endpoints:
`‖z t - segCentre … t‖ ≤ segRadius … t` for every `t` in segment `i`.

`ODE.node_invariant` supplies the enclosure at the left endpoint of the segment, and
`ODE.segment_estimate_at` carries it to an arbitrary interior time. -/
theorem tube_enclosure {k : ℕ} {t₀ T : ℚ}
    (sch : Schedule k t₀ T) {f g : ℝ → (ℝ^k) → ℝ^k} {m : ℚ → (ℚ^k) → ℚ^k}
    {Ω : Set (ℝ × ℝ^k)} {εz εm K M : ℚ} {x₀ : ℚ^k} {ρ₀ : ℚ}
    {W : Fin (sch.p + 1) → Node k}
    (hrun : ∀ i, nodeAt sch m x₀ ρ₀ εz εm K M i = some (W i))
    (hseg : ∀ (i : Fin sch.p) (c : ℚ^k), SegmentCert sch f m Ω εm K M i c)
    {z : ℝ → ℝ^k} (D : DigitalTwin z f g Ω εz t₀ T)
    (hmeas : MeasuredBy z sch)
    (hprior : ‖z (t₀ : ℝ) - (x₀ : ℝ^k)‖ ≤ (ρ₀ : ℝ)) :
    ∀ (i : Fin sch.p), ∀ t ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ),
      ‖z t - segCentre sch m i (W i.castSucc).1 t‖
        ≤ segRadius sch εz εm K M i (W i.castSucc).2 t := by
  have hρ := node_invariant sch hrun hseg D hmeas hprior
  intro i t ht
  have hcert := hseg i (W i.castSucc).1
  have hssub : Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ) ⊆ Set.Icc (t₀ : ℝ) (T : ℝ) :=
    fun s hs => ⟨le_trans (time_mem_schedule sch i.castSucc).1 hs.1,
                 le_trans hs.2 (time_mem_schedule sch i.succ).2⟩
  have hzsub : ∀ s ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ),
      HasDerivWithinAt z (g s (z s)) (Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ)) s :=
    fun s hs => (D.hz.2 s (hssub hs)).mono hssub
  exact segment_estimate_at hcert.hy.2 hzsub (ρ := ((W i.castSucc).2 : ℝ))
    (fun s hs => D.hfg s (hssub hs) (hcert.y s) (hcert.hyΩ s hs))
    (by rw [hcert.hy.1]; exact hρ i.castSucc)
    ht (hcert.hEB t ht)


/-- Drift detection: a failed tube construction refutes the twin.

If `ODE.BuildTube` returns `none` then there is *no* trajectory `z` that is a digital
twin of `f` within `εz`, is consistent with the measurements, and starts within `ρ₀`
of `x₀`.

Contrapositive of `ODE.node_invariant`: such a `z` would force every node to succeed
(each `Rec` has a state to enclose, so `ODE.rec_refute` forbids `none`), in particular
the last one — contradicting `BuildTube = none`.

This is the operationally useful direction. A failed run is positive evidence that the
model has drifted outside its declared error budget, not merely an inconclusive
computation. -/
theorem drift_sound {k : ℕ} {t₀ T : ℚ}
    (sch : Schedule k t₀ T) {f g : ℝ → (ℝ^k) → ℝ^k} {m : ℚ → (ℚ^k) → ℚ^k}
    {Ω : Set (ℝ × ℝ^k)} {εz εm K M : ℚ} {x₀ : ℚ^k} {ρ₀ : ℚ}
    (hseg : ∀ (i : Fin sch.p) (c : ℚ^k), SegmentCert sch f m Ω εm K M i c)
    (hdrift : BuildTube sch m x₀ ρ₀ εz εm K M = none) :
    ¬ ∃ z : ℝ → ℝ^k,
        Nonempty (DigitalTwin z f g Ω εz t₀ T) ∧ MeasuredBy z sch ∧
        ‖z (t₀ : ℝ) - (x₀ : ℝ^k)‖ ≤ (ρ₀ : ℝ) := by
  rintro ⟨z, ⟨D⟩, hmeas, hprior⟩
  have hreach : ∀ i : Fin (sch.p + 1), ∃ q : Node k,
      nodeAt sch m x₀ ρ₀ εz εm K M i = some q ∧
      ‖z (sch.τ i : ℝ) - ((q.1 : ℚ^k) : ℝ^k)‖ ≤ ((q.2 : ℚ) : ℝ) := by
    refine Fin.induction ?_ ?_
    · have hball : ‖z (sch.τ 0 : ℝ) - ((x₀ : ℚ^k) : ℝ^k)‖ ≤ ((ρ₀ : ℚ) : ℝ) := by
        rw [sch.hfirst]; exact hprior
      have hmem := hmeas 0
      cases hq : Rec x₀ ρ₀ (sch.A 0) (sch.B 0) with
      | none => exact (rec_refute hq _ hmem hball).elim
      | some q =>
          obtain ⟨c', r'⟩ := q
          exact ⟨(c', r'), by rw [nodeAt_zero]; exact hq, rec_sound hq _ hmem hball⟩
    · intro i ih
      obtain ⟨q, hq, hinv⟩ := ih
      obtain ⟨c, ρ⟩ := q
      have hcert := hseg i c
      have hssub : Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ)
          ⊆ Set.Icc (t₀ : ℝ) (T : ℝ) := by
        intro s hs
        exact ⟨le_trans (time_mem_schedule sch i.castSucc).1 hs.1,
               le_trans hs.2 (time_mem_schedule sch i.succ).2⟩
      have hzsub : ∀ s ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ),
          HasDerivWithinAt z (g s (z s)) (Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ)) s :=
        fun s hs => (D.hz.2 s (hssub hs)).mono hssub
      have hpre : ‖z (sch.τ i.succ : ℝ)
                    - (((segEnd sch m εz εm K M i c ρ).1 : ℚ^k) : ℝ^k)‖
                  ≤ (((segEnd sch m εz εm K M i c ρ).2 : ℚ) : ℝ) := by
        have hat := segment_estimate_at hcert.hy.2 hzsub (ρ := (ρ : ℝ))
          (fun s hs => D.hfg s (hssub hs) (hcert.y s) (hcert.hyΩ s hs))
          (by rw [hcert.hy.1]; exact hinv)
          (t := (sch.τ i.succ : ℝ))
          (by simp only [Set.mem_Icc, Rat.cast_le, le_refl, and_true]
              exact_mod_cast (sch.hmono (Fin.castSucc_lt_succ)).le)
          (EBt := EB K εm M (sch.δ i) (sch.N i))
          (Ct := (LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) c m (sch.N i)
                   (sch.hN i) (sch.hmono (Fin.castSucc_lt_succ))).x (sch.N i))
          (by
            have hEB := hcert.hEB (sch.τ i.succ : ℝ)
                (Set.right_mem_Icc.mpr (by exact_mod_cast (sch.hmono (Fin.castSucc_lt_succ)).le))
            simp only at hEB
            set S := LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) c m (sch.N i)
                (sch.hN i) (sch.hmono (Fin.castSucc_lt_succ)) with hS
            have : sch.τ i.succ = S.t (sch.N i) := by
              simp only [VectorScheme.t, hS, LastVectorSchema]
              rw [IsUnit.mul_div_cancel _ (sch.τ i.succ - sch.τ i.castSucc)]
              · simp only [add_sub_cancel]
              · simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, sch.hN,
                not_false_eq_true]
            rw [this] at hEB
            rw [VectorScheme.plR_grid] at hEB
            rw [← this] at hEB
            exact hEB)
        push_cast
        push_cast at hat
        simp only [segEnd, Rat.cast_add, Rat.cast_mul, ge_iff_le]
        set S := LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) c m (sch.N i)
            (sch.hN i) (sch.hmono (Fin.castSucc_lt_succ)) with hS
        simp only [Schedule.h]
        push_cast
        grind
      have hmem := hmeas i.succ
      cases hq' : Rec (segEnd sch m εz εm K M i c ρ).1 (segEnd sch m εz εm K M i c ρ).2
                      (sch.A i.succ) (sch.B i.succ) with
      | none => exact (rec_refute hq' _ hmem hpre).elim
      | some q' =>
          obtain ⟨c'', r''⟩ := q'
          refine ⟨(c'', r''), ?_, rec_sound hq' _ hmem hpre⟩
          simp only [nodeAt_succ, hq, Option.bind_some]
          exact hq'
  obtain ⟨q, hq, -⟩ := hreach (Fin.last sch.p)
  simp only [BuildTube, hq] at hdrift
  grind

/-- The segments of a schedule cover `[t₀, T]`: every time lies in some `[τ i, τ (i+1)]`.

Take the largest node `j` with `τ j ≤ t`. If `j` is the last node then `t = T` and the
final segment works; otherwise maximality of `j` gives `t ≤ τ (j+1)`, so segment `j`
works. The endpoints are included on both sides, so consecutive segments overlap at
their shared node and no time is missed. -/
theorem Schedule.exists_seg {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)
    {t : ℝ} (ht : t ∈ Set.Icc (t₀ : ℝ) (T : ℝ)) :
    ∃ i : Fin sch.p,
      (sch.τ i.castSucc : ℝ) ≤ t ∧ t ≤ (sch.τ i.succ : ℝ) := by
    set S := Finset.univ.filter (fun j : Fin (sch.p + 1) => (sch.τ j : ℝ) ≤ t) with hS
    have h0 : (0 : Fin (sch.p + 1)) ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, sch.hfirst]
      exact ht.1
    have hSne : S.Nonempty := ⟨0, h0⟩
    set j := S.max' hSne with hjdef
    have hjle : (sch.τ j : ℝ) ≤ t := (Finset.mem_filter.mp (S.max'_mem hSne)).2
    rcases eq_or_lt_of_le (Fin.le_last j) with hj | hj
    · have hple : sch.p - 1 < sch.p := by simp only [tsub_lt_self_iff, Order.lt_one_iff, and_true]
                                          apply Nat.pos_of_ne_zero sch.hp
      refine ⟨⟨sch.p - 1, Nat.sub_lt (Nat.pos_of_ne_zero sch.hp) one_pos⟩, ?_, ?_⟩
      · refine le_trans ?_ (hj ▸ hjle)
        exact_mod_cast sch.hmono.monotone (by simp [Fin.le_def])
      · have hsucc : (⟨sch.p - 1, Nat.sub_lt (Nat.pos_of_ne_zero sch.hp) one_pos⟩
                        : Fin sch.p).succ = Fin.last sch.p := by
          apply Fin.ext
          simp [Fin.val_last]
          omega
        rw [hsucc, sch.hlast]
        exact ht.2
    · have hjp : (j : ℕ) < sch.p := by
        simpa [Fin.lt_def, Fin.val_last] using hj
      refine ⟨⟨j, hjp⟩, ?_, ?_⟩
      · have : (⟨(j : ℕ), hjp⟩ : Fin sch.p).castSucc = j := by
          apply Fin.ext; simp
        rw [this]; exact hjle
      · by_contra hcon
        push Not at hcon
        have hmem : (⟨(j : ℕ), hjp⟩ : Fin sch.p).succ ∈ S := by
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hcon.le
        have := Finset.le_max' S _ hmem
        rw [← hjdef] at this
        simp [Fin.le_def] at this

/-- Global form of `ODE.tube_enclosure`: the twin is in the tube at *every* time of
`[t₀, T]`.

Combines the per-segment enclosure with `ODE.Schedule.exists_seg`, which locates an
arbitrary time inside some segment. This is the headline guarantee of the digital-twin
machinery: a successful `ODE.BuildTube` run certifies a tube that provably contains the
real trajectory for the entire horizon. -/
theorem tube_enclosure_global {k : ℕ} {t₀ T : ℚ}
    (sch : Schedule k t₀ T) {f g : ℝ → (ℝ^k) → ℝ^k} {m : ℚ → (ℚ^k) → ℚ^k}
    {Ω : Set (ℝ × ℝ^k)} {εz εm K M : ℚ} {x₀ : ℚ^k} {ρ₀ : ℚ}
    {W : Fin (sch.p + 1) → Node k}
    (hrun : ∀ i, nodeAt sch m x₀ ρ₀ εz εm K M i = some (W i))
    (hseg : ∀ (i : Fin sch.p) (c : ℚ^k), SegmentCert sch f m Ω εm K M i c)
    {z : ℝ → ℝ^k} (D : DigitalTwin z f g Ω εz t₀ T)
    (hmeas : MeasuredBy z sch)
    (hprior : ‖z (t₀ : ℝ) - (x₀ : ℝ^k)‖ ≤ (ρ₀ : ℝ)) :
    ∀ t ∈ Set.Icc (t₀ : ℝ) (T : ℝ), ∃ i : Fin sch.p,
      ‖z t - segCentre sch m i (W i.castSucc).1 t‖
        ≤ segRadius sch εz εm K M i (W i.castSucc).2 t := by
  intro t ht
  obtain ⟨i, hi⟩ := sch.exists_seg ht
  exact ⟨i, tube_enclosure sch hrun hseg D hmeas hprior i t hi⟩





end ODE
