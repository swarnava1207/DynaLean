module

public import Mathlib
public import DynaLean.Defs

@[expose] public section

/-! # Euler schemes on a rational grid

An *Euler scheme* is the data needed to run the explicit Euler method: a step size `δ`,
a start time `t₀`, an initial value `x₀`, and a model field `m`. Everything is rational,
so the grid times `tₙ`, the iterates `xₙ` and the piecewise-linear interpolant are
*exactly* computable — no floating point is involved anywhere, and `#eval` or `decide`
can evaluate them. The comparison with a real solution happens only later, in
`DynaLean.EulerBound`, through the coercion `ℚ → ℝ`.

This module provides:

* `Scheme` / `VectorScheme n` — the scheme data, scalar and `ℚ^n`-valued;
* `Scheme.t`, `Scheme.x` — the grid `tₙ = t₀ + n δ` and the iterates
  `xₙ₊₁ = xₙ + δ · m tₙ xₙ`;
* `Scheme.lOn`, `Scheme.idx`, `Scheme.pl` — the affine piece on a cell, the index of the
  cell containing a time, and the resulting piecewise-linear interpolant;
* `Scheme.plR`, `Scheme.idxR`, `Scheme.plRR` (and `VectorScheme.plR`) — real-valued
  views of the interpolant, which is what the error theorems actually bound;
* the basic rewriting lemmas relating all of these.

The `VectorScheme` half of the file mirrors the scalar half declaration for
declaration, with `*` replaced by the scalar action `•`.
-/

/-- The Euler schema initial details packed as a `structure`.

All four pieces of data are rational, which is what makes `Scheme.x` exactly
computable. -/
structure Scheme where
  /-- The step size. Positive by `hδ`. -/
  δ : ℚ
  /-- Positivity of the step size. -/
  hδ : 0 < δ
  /-- The initial time, i.e. the left end of the grid. -/
  t₀ : ℚ
  /-- The initial value `x 0`. -/
  x₀ : ℚ
  /-- The model field: `m t x` is the slope used by the Euler step taken at time `t`
  from state `x`. It stands in for the true vector field `f`, and the error theorems
  charge the difference `|f - m|` to the model-error budget `ε`. -/
  m  : ℚ → ℚ → ℚ

namespace Scheme

variable (S : Scheme)

/-- The time grid `tₙ = t₀ + n·δ`. -/
@[simp]
def t (n : ℕ) : ℚ := S.t₀ + (n : ℚ) * S.δ

/-- The Euler iterates `x₀`, `x_{n+1} = xₙ + δ · m(xₙ, tₙ)`. -/
@[simp]
def x : ℕ → ℚ
  | 0     => S.x₀
  | n + 1 => x n + S.δ * S.m (S.t n) (x n)

/-- The affine piece carried by the `n`-th subinterval `[tₙ, tₙ₊₁]`,
evaluated at an arbitrary time `s`. -/
def lOn (n : ℕ) (s : ℚ) : ℚ :=
  S.x n + (s - S.t n) * S.m (S.t n) (S.x n)

/-- Index of the subinterval containing `s`: the unique `n` with
`tₙ ≤ s < tₙ₊₁` when `s ≥ t₀`, and `0` for `s < t₀`. -/
def idx (s : ℚ) : ℕ := ⌊(s - S.t₀) / S.δ⌋.toNat

/-- The piecewise-linear interpolant `x̃`. Computable: every ingredient is rational. -/
def pl (s : ℚ) : ℚ := S.lOn (S.idx s) s

/-- Interpolant clamped to the first `N` steps (constant-slope extension past `t_N`
is avoided; useful when the theorem is stated on `[t₀, T]` with `T = t_N`). -/
def plClamp (N : ℕ) (s : ℚ) : ℚ := S.lOn (min N (S.idx s)) s

/-- Real-valued view of the interpolant, for comparison with the exact solution.

Still indexed by a *rational* time; use `Scheme.plRR` when the time itself is real. -/
def plR (s : ℚ) : ℝ := (S.pl s : ℝ)

/-- `Scheme.idx` for a real time: the index `n` of the grid cell `[tₙ, tₙ₊₁]` containing
`s`, and `0` for `s < t₀`.

Noncomputable because the floor is taken in `ℝ`; `Scheme.idxR_eq_of_mem_Ico` is what
lets proofs evaluate it anyway. -/
noncomputable def idxR (s : ℝ) : ℕ := ⌊((s - S.t₀) / S.δ : ℝ)⌋.toNat

/-- The piecewise-linear interpolant evaluated at a *real* time.

This is the function that `ODE.euler_bound_solution_all` compares with the exact
solution at every `s ∈ [t₀, T]`, as opposed to only at grid points. -/
noncomputable def plRR (s : ℝ) : ℝ :=
  (S.x (S.idxR s) : ℝ) + (s - (S.t (S.idxR s) : ℝ)) * (S.m (S.t (S.idxR s)) (S.x (S.idxR s)) : ℝ)

/-! ### Basic rewriting lemmas -/

/-- The first grid time is the initial time. -/
@[simp] theorem t_zero : S.t 0 = S.t₀ := by simp [t]

/-- Each successive grid time is one step size after the preceding time. -/
theorem t_succ (n : ℕ) : S.t (n + 1) = S.t n + S.δ := by
  simp [t, add_mul]; ring

/-- The grid-time definition expanded into its closed form. -/
theorem t_succ' (n : ℕ) : S.t n = S.t₀ + (n : ℚ) * S.δ := by
  induction n with
  | zero => simp [t]
  | succ n ih =>
      have : S.t (n + 1) = S.t n + S.δ := by simp [t, add_mul]; ring
      rw [this, ih]
      push_cast
      ring

/-- The zeroth Euler iterate is the initial value. -/
@[simp] theorem x_zero : S.x 0 = S.x₀ := rfl

/-- Each Euler iterate is obtained from the preceding iterate by one Euler step. -/
@[simp] theorem x_succ (n : ℕ) : S.x (n + 1) = S.x n + S.δ * S.m (S.t n) (S.x n) := rfl

/-- The affine piece starts at the Euler iterate for its left endpoint. -/
@[simp] theorem plOn_left (n : ℕ) : S.lOn n (S.t n) = S.x n := by
  simp only [lOn, t, sub_self, zero_mul, add_zero]

/-- The pieces agree at the shared node: the interpolant is continuous. -/
theorem plOn_right (n : ℕ) : S.lOn n (S.t (n + 1)) = S.x (n + 1) := by
  simp only [lOn, t_succ, add_sub_cancel_left, x_succ]

/-- On its own subinterval, `idx` picks out the right piece. -/
theorem idx_eq_of_mem_Ico {n : ℕ} {s : ℚ} (h₁ : S.t n ≤ s) (h₂ : s < S.t (n + 1)) :
    S.idx s = n := by
  unfold idx
  have triv : (S.t n - S.t₀)/ S.δ = (n : ℚ) := by
    calc
      (S.t n - S.t₀)/S.δ = ((S.t₀ + (n : ℚ) * S.δ) - S.t₀)/S.δ := by simp [t]
      _ = (n : ℚ) * S.δ / S.δ := by ring
      _ = (n : ℚ) := by field_simp [S.hδ.ne']
  by_cases h : (s - S.t₀) / S.δ < 0
  · have : S.t n ≥ S.t₀ := by simp [t, hδ]
    have : S.t n ≤ s := by linarith
    have : s < S.t₀ := by field_simp [t, hδ] at h; linarith
    grind
  · have : (s - S.t₀)/S.δ = (s - S.t n)/S.δ + (n : ℚ) := by
      calc
        (s - S.t₀)/S.δ = (s - S.t n)/S.δ + (S.t n - S.t₀)/S.δ := by field_simp [t, hδ]; grind
        _ = (s - S.t n)/S.δ + (n : ℚ) := by grind
    rw [this]
    rw [Int.floor_add_natCast]
    have ge_0 : 0 ≤ (s - S.t n)/S.δ := by
        rw [div_nonneg_iff]
        apply Or.inl
        apply And.intro (by linarith) S.hδ.le
    have lt_1 : (s - S.t n)/S.δ < 1 := by
      calc
        (s - S.t n)/S.δ < (S.t (n + 1) - S.t n)/S.δ := by
          apply (div_lt_div_iff_of_pos_right S.hδ ).2; linarith
        _ = 1 := by simp only [t_succ, add_sub_cancel_left, div_self_eq_one₀, ne_eq]; exact S.hδ.ne'
    have : Int.floor ((s - S.t n)/S.δ) = 0 := by
      apply Int.floor_eq_zero_iff.2 ⟨ge_0, lt_1⟩
    rw [this]; simp only [zero_add, Int.toNat_natCast]

/-- Real-time version of `Scheme.idx_eq_of_mem_Ico`: on the cell `[tₙ, tₙ₊₁)`, `idxR`
returns `n`. -/
theorem idxR_eq_of_mem_Ico {n : ℕ} {s : ℝ} (h₁ : S.t n ≤ s) (h₂ : s < S.t (n + 1)) :
    S.idxR s = n := by
  simp only [idxR]
  have pos : 0 < (S.δ : ℝ) := by exact_mod_cast S.hδ
  have spos : 0 ≤ (s - S.t₀) / (S.δ : ℝ) := by
    apply div_nonneg _ pos.le
    simp only [sub_nonneg]
    apply le_trans _ h₁
    simp only [t, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, le_add_iff_nonneg_right]
    positivity
  rw [Int.floor_toNat]
  rw [Nat.floor_eq_iff spos]
  field_simp
  simp only [t] at h₁ h₂
  push_cast at h₁ h₂
  grind

/-- On a grid subinterval, the interpolant equals its affine piece. -/
theorem pl_eq_plOn_of_mem_Ico {n : ℕ} {s : ℚ} (h₁ : S.t n ≤ s) (h₂ : s < S.t (n + 1)) :
    S.pl s = S.lOn n s := by
  rw [pl, S.idx_eq_of_mem_Ico h₁ h₂]

/-- The interpolant hits the Euler data at every grid point. -/
theorem pl_grid (n : ℕ) : S.pl (S.t n) = S.x n := by
  rw [S.pl_eq_plOn_of_mem_Ico (le_refl _) (by rw [t_succ]; linarith [S.hδ]),
      plOn_left]

/-- Every grid point of the first `⌊(T - t₀)/δ⌋ + 1` lies in `[t₀, T]`.

This is the side condition that lets the error theorems quantify over
`Finset.range (⌊(T - S.t₀) / S.δ⌋₊ + 1)` while still applying hypotheses that are only
available on `[t₀, T]`. -/
theorem time_mem (T : ℚ) (hT : S.t₀ ≤ T) :
 ∀ n ∈ Finset.range (⌊(T - S.t₀)/S.δ⌋₊ + 1), (S.t n : ℝ) ∈ Set.Icc (S.t₀ : ℝ) (T : ℝ) := by
 intro n hn
 induction n with
 | zero => simp only [t, CharP.cast_eq_zero, zero_mul, add_zero, Set.mem_Icc, Std.le_refl,
   Rat.cast_le, hT, and_self]
 | succ n ih =>
    specialize ih (by grind)
    have from_ih : (S.t (n + 1) : ℝ) = S.t n + S.δ := by simp [t, add_mul]; ring
    rw [from_ih]
    rw [Set.mem_Icc]
    apply And.intro (le_trans ih.1 (by apply le_add_of_nonneg_right (by exact_mod_cast S.hδ.le)))
    have hnf : n + 1 < ⌊(T - S.t₀)/S.δ⌋₊ + 1 := Finset.mem_range.1 hn
    simp only [t, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, ge_iff_le]
    have : n + 1 ≤ (T - S.t₀)/S.δ := by
      norm_cast
      apply Nat.le_of_lt_succ at hnf
      rw [← Nat.le_floor_iff' (by grind)]
      exact hnf
    norm_cast
    rw [le_div_iff₀ S.hδ] at this
    grind
end Scheme

section VectorScheme

/-! ## Euler schemes for systems

`VectorScheme n` repeats `Scheme` with the state space `ℚ^n` in place of `ℚ`. Every
declaration below is the exact analogue of the scalar one above; the only difference is
that the Euler update uses the scalar action `δ • m tₙ xₙ` rather than multiplication. -/

/-- The Euler schema initial details for an `n`-dimensional system, packed as a
`structure`.

The `ℚ^n` analogue of `Scheme`: still entirely rational, hence still exactly
computable. -/
structure VectorScheme (n : ℕ) where
  /-- The step size. Positive by `hδ`. -/
  δ : ℚ
  /-- Positivity of the step size. -/
  hδ : 0 < δ
  /-- The initial time, i.e. the left end of the grid. -/
  t₀ : ℚ
  /-- The initial state vector `x 0`. -/
  x₀ : ℚ^n
  /-- The model field: `m t x` is the slope vector used by the Euler step taken at time
  `t` from state `x`. -/
  m  : ℚ → (ℚ^n) → ℚ^n


namespace VectorScheme
variable {k : ℕ} (S : VectorScheme k)

/-- The time grid `tₙ = t₀ + n·δ`. The `ℚ^k` analogue of `Scheme.t`. -/
def t (k : ℕ) : ℚ := S.t₀ + (k : ℚ) * S.δ

/-- The Euler iterates `x₀`, `x_{n+1} = xₙ + δ • m(tₙ, xₙ)`.

The `ℚ^k` analogue of `Scheme.x`; the step uses the scalar action `•` on `ℚ^k`. -/
def x : ℕ → ℚ^k
  | 0     => S.x₀
  | k + 1 => x k + S.δ • S.m (S.t k) (x k)


/-- The affine piece carried by the `n`-th subinterval `[tₙ, tₙ₊₁]`,
evaluated at an arbitrary time `s`. -/
def lOn (m : ℕ) (s : ℚ) : ℚ^k :=
  S.x m + (s - S.t m) • (S.m (S.t m) (S.x m))

/-- Index of the subinterval containing `s`: the unique `n` with
`tₙ ≤ s < tₙ₊₁` when `s ≥ t₀`, and `0` for `s < t₀`. -/
def idx (s : ℚ) : ℕ := ⌊(s - S.t₀) / S.δ⌋.toNat

/-- `VectorScheme.idx` for a real time; the `ℚ^k` analogue of `Scheme.idxR`.

Noncomputable because the floor is taken in `ℝ`; use
`VectorScheme.idxR_eq_of_mem_Ico` to evaluate it in proofs. -/
noncomputable def idxR (s : ℝ) : ℕ := ⌊((s - S.t₀) / S.δ : ℝ)⌋.toNat

/-- The piecewise-linear interpolant `x̃`. Computable: every ingredient is rational. -/
def pl (s : ℚ) : ℚ^k := S.lOn (S.idx s) s

/-- Interpolant clamped to the first `N` steps (constant-slope extension past `t_N`
is avoided; useful when the theorem is stated on `[t₀, T]` with `T = t_N`). -/
def plClamp (N : ℕ) (s : ℚ) : ℚ^k := S.lOn (min N (S.idx s)) s

/-- Real-valued view of the interpolant, for comparison with the exact solution.

Unlike the scalar `Scheme.plR`, this already takes a *real* time, so it plays the role
of `Scheme.plRR`: it is the curve bounded by
`ODE.euler_bound_solution_all_vector` and used as the tube centre in
`ODE.segCentre`. -/
noncomputable def plR (s : ℝ) : ℝ^k := S.x (S.idxR s) +
  ((s - S.t (S.idxR s)) : ℝ) • (S.m (S.t (S.idxR s)) (S.x (S.idxR s)))

/-! ### Basic rewriting lemmas -/

/-- The first grid time is the initial time. -/
@[simp] theorem t_zero : S.t 0 = S.t₀ := by simp [t]

/-- Each successive grid time is one step size after the preceding time. -/
theorem t_succ (n : ℕ) : S.t (n + 1) = S.t n + S.δ := by
  simp [t, add_mul]; ring

/-- The grid-time definition expanded into its closed form. -/
theorem t_succ' (n : ℕ) : S.t n = S.t₀ + (n : ℚ) * S.δ := by
  induction n with
  | zero => simp [t]
  | succ n ih =>
      have : S.t (n + 1) = S.t n + S.δ := by simp [t, add_mul]; ring
      rw [this, ih]
      push_cast
      ring

/-- The zeroth Euler iterate is the initial value. -/
@[simp] theorem x_zero : S.x 0 = S.x₀ := rfl

/-- Each Euler iterate is obtained from the preceding iterate by one Euler step. -/
@[simp] theorem x_succ (n : ℕ) : S.x (n + 1) = S.x n + S.δ • S.m (S.t n) (S.x n) := rfl

/-- The affine piece starts at the Euler iterate for its left endpoint. -/
@[simp] theorem plOn_left (n : ℕ) : S.lOn n (S.t n) = S.x n := by
  simp only [lOn, t, sub_self]
  simp only [zero_smul, add_zero]

/-- The pieces agree at the shared node: the interpolant is continuous. -/
theorem plOn_right (n : ℕ) : S.lOn n (S.t (n + 1)) = S.x (n + 1) := by
  simp only [lOn, t_succ, add_sub_cancel_left, x_succ]

/-- On its own subinterval, `idx` picks out the right piece. -/
theorem idx_eq_of_mem_Ico {n : ℕ} {s : ℚ} (h₁ : S.t n ≤ s) (h₂ : s < S.t (n + 1)) :
    S.idx s = n := by
  unfold idx
  have triv : (S.t n - S.t₀)/ S.δ = (n : ℚ) := by
    calc
      (S.t n - S.t₀)/S.δ = ((S.t₀ + (n : ℚ) * S.δ) - S.t₀)/S.δ := by simp [t]
      _ = (n : ℚ) * S.δ / S.δ := by ring
      _ = (n : ℚ) := by field_simp [S.hδ.ne']
  by_cases h : (s - S.t₀) / S.δ < 0
  · have : S.t n ≥ S.t₀ := by simp [t, hδ]
    have : S.t n ≤ s := by linarith
    have : s < S.t₀ := by field_simp [t, hδ] at h; linarith
    grind
  · have : (s - S.t₀)/S.δ = (s - S.t n)/S.δ + (n : ℚ) := by
      calc
        (s - S.t₀)/S.δ = (s - S.t n)/S.δ + (S.t n - S.t₀)/S.δ := by field_simp [t, hδ]; grind
        _ = (s - S.t n)/S.δ + (n : ℚ) := by grind
    rw [this]
    rw [Int.floor_add_natCast]
    have ge_0 : 0 ≤ (s - S.t n)/S.δ := by
        rw [div_nonneg_iff]
        apply Or.inl
        apply And.intro (by linarith) S.hδ.le
    have lt_1 : (s - S.t n)/S.δ < 1 := by
      calc
        (s - S.t n)/S.δ < (S.t (n + 1) - S.t n)/S.δ := by
          apply (div_lt_div_iff_of_pos_right S.hδ ).2; linarith
        _ = 1 := by simp only [t_succ, add_sub_cancel_left, div_self_eq_one₀, ne_eq]; exact S.hδ.ne'
    have : Int.floor ((s - S.t n)/S.δ) = 0 := by
      apply Int.floor_eq_zero_iff.2 ⟨ge_0, lt_1⟩
    rw [this]; simp only [zero_add, Int.toNat_natCast]

/-- Real-time version of `VectorScheme.idx_eq_of_mem_Ico`: on the cell `[tₙ, tₙ₊₁)`,
`idxR` returns `n`. -/
theorem idxR_eq_of_mem_Ico {n : ℕ} {s : ℝ} (h₁ : S.t n ≤ s) (h₂ : s < S.t (n + 1)) :
    S.idxR s = n := by
  simp only [idxR]
  rw [Int.floor_toNat]
  have pos : 0 < (S.δ : ℝ) := by exact_mod_cast S.hδ
  have spos : 0 ≤ (s - S.t₀) / (S.δ : ℝ) := by
    apply div_nonneg _ pos.le
    simp only [sub_nonneg]
    apply le_trans _ h₁
    simp only [t, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, le_add_iff_nonneg_right]
    positivity
  rw [Nat.floor_eq_iff spos]
  field_simp
  simp only [t] at h₁ h₂
  push_cast at h₁ h₂
  grind

/-- On a grid subinterval, the interpolant equals its affine piece. -/
theorem pl_eq_plOn_of_mem_Ico {n : ℕ} {s : ℚ} (h₁ : S.t n ≤ s) (h₂ : s < S.t (n + 1)) :
    S.pl s = S.lOn n s := by
  rw [pl, S.idx_eq_of_mem_Ico h₁ h₂]

/-- The interpolant hits the Euler data at every grid point. -/
theorem pl_grid (n : ℕ) : S.pl (S.t n) = S.x n := by
  rw [S.pl_eq_plOn_of_mem_Ico (le_refl _) (by rw [t_succ]; linarith [S.hδ]),
      plOn_left]

/-- At a grid point the real-valued interpolant returns the Euler iterate exactly.

The real-time counterpart of `VectorScheme.pl_grid`, used to transfer grid-point error
bounds to the interpolant. -/
theorem plR_grid (n : ℕ) : S.plR ((S.t n) : ℝ) = (S.x n : ℝ^k) := by
  simp only [plR]
  have h := idxR_eq_of_mem_Ico S (n := n) (le_refl _)
    (by rw [t_succ]; push_cast; simp only [lt_add_iff_pos_right,
    Rat.cast_pos]; exact_mod_cast S.hδ)
  rw [h]
  simp only [WithLp.equiv_symm_apply, sub_self, zero_smul, add_zero]

/-- Every grid point of the first `⌊(T - t₀)/δ⌋ + 1` lies in `[t₀, T]`.

The `ℚ^k` analogue of `Scheme.time_mem`. -/
theorem time_mem (T : ℚ) (hT : S.t₀ ≤ T) :
 ∀ n ∈ Finset.range (⌊(T - S.t₀)/S.δ⌋₊ + 1), (S.t n : ℝ) ∈ Set.Icc (S.t₀ : ℝ) (T : ℝ) := by
 intro n hn
 induction n with
 | zero => simp only [t, CharP.cast_eq_zero, zero_mul, add_zero, Set.mem_Icc, Std.le_refl,
   Rat.cast_le, hT, and_self]
 | succ n ih =>
    specialize ih (by grind)
    have from_ih : (S.t (n + 1) : ℝ) = S.t n + S.δ := by simp [t, add_mul]; ring
    rw [from_ih]
    rw [Set.mem_Icc]
    apply And.intro (le_trans ih.1 (by apply le_add_of_nonneg_right (by exact_mod_cast S.hδ.le)))
    have hnf : n + 1 < ⌊(T - S.t₀)/S.δ⌋₊ + 1 := Finset.mem_range.1 hn
    simp only [t, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, ge_iff_le]
    have : n + 1 ≤ (T - S.t₀)/S.δ := by
      norm_cast
      apply Nat.le_of_lt_succ at hnf
      rw [← Nat.le_floor_iff' (by grind)]
      exact hnf
    norm_cast
    rw [le_div_iff₀ S.hδ] at this
    grind

end VectorScheme
