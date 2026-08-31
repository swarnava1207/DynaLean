import Mathlib

structure Scheme where
  δ : ℚ
  hδ : 0 < δ
  t₀ : ℚ
  x₀ : ℚ
  m  : ℚ → ℚ → ℚ

namespace Scheme

variable (S : Scheme)

/-- The time grid `tₙ = t₀ + n·δ`. -/
def t (n : ℕ) : ℚ := S.t₀ + (n : ℚ) * S.δ

/-- The Euler iterates `x₀`, `x_{n+1} = xₙ + δ · m(xₙ, tₙ)`. -/
def x : ℕ → ℚ
  | 0     => S.x₀
  | n + 1 => x n + S.δ * S.m (S.t n) (x n)

/-- The affine piece carried by the `n`-th subinterval `[tₙ, tₙ₊₁]`,
evaluated at an arbitrary time `s`. -/
def plOn (n : ℕ) (s : ℚ) : ℚ :=
  S.x n + (s - S.t n) * S.m (S.t n) (S.x n)

/-- Index of the subinterval containing `s`: the unique `n` with
`tₙ ≤ s < tₙ₊₁` when `s ≥ t₀`, and `0` for `s < t₀`. -/
def idx (s : ℚ) : ℕ := ⌊(s - S.t₀) / S.δ⌋.toNat

/-- The piecewise-linear interpolant `x̃`. Computable: every ingredient is rational. -/
def pl (s : ℚ) : ℚ := S.plOn (S.idx s) s

/-- Interpolant clamped to the first `N` steps (constant-slope extension past `t_N`
is avoided; useful when the theorem is stated on `[t₀, T]` with `T = t_N`). -/
def plClamp (N : ℕ) (s : ℚ) : ℚ := S.plOn (min N (S.idx s)) s

/-- Real-valued view of the interpolant, for comparison with the exact solution. -/
def plR (s : ℚ) : ℝ := (S.pl s : ℝ)

/-! ### Basic rewriting lemmas -/

@[simp] theorem t_zero : S.t 0 = S.t₀ := by simp [t]

theorem t_succ (n : ℕ) : S.t (n + 1) = S.t n + S.δ := by
  simp [t, add_mul]; ring

theorem t_succ' (n : ℕ) : S.t n = S.t₀ + (n : ℚ) * S.δ := by
  induction n with
  | zero => simp [t]
  | succ n ih =>
      have : S.t (n + 1) = S.t n + S.δ := by simp [t, add_mul]; ring
      rw [this, ih]
      push_cast
      ring

@[simp] theorem x_zero : S.x 0 = S.x₀ := rfl

theorem x_succ (n : ℕ) : S.x (n + 1) = S.x n + S.δ * S.m (S.t n) (S.x n) := rfl

@[simp] theorem plOn_left (n : ℕ) : S.plOn n (S.t n) = S.x n := by
  simp [plOn]

/-- The pieces agree at the shared node: the interpolant is continuous. -/
theorem plOn_right (n : ℕ) : S.plOn n (S.t (n + 1)) = S.x (n + 1) := by
  simp [plOn, x_succ, t_succ]

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
    rw [this]; simp


theorem pl_eq_plOn_of_mem_Ico {n : ℕ} {s : ℚ} (h₁ : S.t n ≤ s) (h₂ : s < S.t (n + 1)) :
    S.pl s = S.plOn n s := by
  rw [pl, S.idx_eq_of_mem_Ico h₁ h₂]

/-- The interpolant hits the Euler data at every grid point. -/
theorem pl_grid (n : ℕ) : S.pl (S.t n) = S.x n := by
  rw [S.pl_eq_plOn_of_mem_Ico (le_refl _) (by rw [t_succ]; linarith [S.hδ]),
      plOn_left]

end Scheme
