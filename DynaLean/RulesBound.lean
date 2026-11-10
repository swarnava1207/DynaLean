module

public import Mathlib
public import DynaLean.Defs
public import DynaLean.EulerScheme
public import DynaLean.EulerBound
public import DynaLean.Rules

/-! # Enclosures that combine the Euler bound with a qualitative rule

`DynaLean.EulerBound` gives a symmetric interval `xₙ ± bound n` around each Euler
iterate. `DynaLean.Rules` gives a region the exact solution can never leave. Neither
implies the other, so intersecting them is strictly better than either.

This module does exactly that, once per rule:

| refinement             | rule used                     | soundness theorem        |
| ---------------------- | ----------------------------- | ------------------------ |
| `ODE.half_line_refine` | `ODE.solution_half_line`      | `ODE.half_line_bound`    |
| `ODE.monotone_refine`  | `ODE.solution_monotone`       | `ODE.monotone_bound`     |
| `ODE.lyapunov_refine`  | `ODE.solution_lyapunov_kind`  | `ODE.lyapunov_bound`     |

The `*_refine` functions are pure rational computations: they take the scheme and the
error budget and return an interval. The `*_bound` theorems say that the exact solution
really lies in that interval at every grid point of `[t₀, T]`.
-/

@[expose] public section

namespace ODE


/-- The sharp Euler error radius after `n` steps:
`(ε + M δ / 2) · δ · ((1 + K δ)ⁿ - 1) / (K δ)`.

An abbreviation for the right-hand side of `ODE.euler_bound_solution_rational`, so the
enclosures below can be written compactly. -/
abbrev bound (n : ℕ) (ε K M δ : ℚ) := ((ε + M * δ / 2) * δ) * (((1 + K*δ) ^ n) - 1)/(K * δ)

/-- Enclosure refined by a lower barrier: intersect `xₙ ± bound n` with the half-line
`[c, ∞)`.

Returns the pair `(max c (xₙ - bound n), xₙ + bound n)`. Sound by
`ODE.half_line_bound` whenever the hypotheses of `ODE.solution_half_line` hold. -/
def half_line_refine (S : Scheme) (ε c K M : ℚ) (n : ℕ) :=
  let Ln := S.x n - bound n ε K M S.δ
  let Un := S.x n + bound n ε K M S.δ
  ((max c Ln),Un)

/-- Enclosure refined by monotonicity: the lower end never decreases along the grid.

Defined by recursion on `n`: the lower end at step `n + 1` is the larger of the lower
end already established at step `n` and the raw `xₙ₊₁ - bound (n+1)`. Since a monotone
solution cannot go back below a level it has passed, carrying the running maximum
forward is sound — see `ODE.monotone_bound`. -/
def monotone_refine (S : Scheme) (ε K M : ℚ) (n : ℕ) :=
  let Ln := S.x n - bound n ε K M S.δ
  let Un := S.x n + bound n ε K M S.δ
  match n with
  | 0 => (Ln, Un)
  | n+1 =>
  (max (monotone_refine S ε K M n).1 Ln, Un)

/-- Enclosure refined by an invariant band: intersect `xₙ ± bound n` with `[-R, R]`.

Returns `(max (-R) (xₙ - bound n), min R (xₙ + bound n))`. Sound by
`ODE.lyapunov_bound` whenever the hypotheses of `ODE.solution_lyapunov_kind` hold. -/
def lyapunov_refine (S : Scheme) (ε R K M : ℚ) (n : ℕ) :=
  let Ln := S.x n - bound n ε K M S.δ
  let Un := S.x n + bound n ε K M S.δ
  ((max (-R) Ln), (min R Un))

section RefineProofs

/-! ## Soundness of the refined enclosures

All three theorems below share the same hypothesis block, collected in the `variable`
command: `y` is an exact solution on `[t₀, T]` which is `C²` with `|y''| ≤ M`, the
field is `K`-Lipschitz in state, the scheme `S` starts at the same `(t₀, x₀)` and its
model field is within `ε` of the true one. These are exactly the hypotheses of
`ODE.euler_bound_solution_rational`, plus whatever the particular rule needs. -/

variable {f : ℝ → ℝ → ℝ} {S : Scheme} {ε x₀ t₀ T K M : ℚ} (hMne : 0 < M) (hKne : 0 < K)
  (hT : t₀ < T)
  (hlip : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
  (hy : SolutionExists f x₀ y (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T))
  (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) T))
  (hm : ∀ t x : ℚ, |f t x - S.m t x| ≤ ε)
  (hiter : ∀ t ∈ Set.Ioo (t₀ : ℝ) T, |iteratedDeriv 2 y t| ≤ M)
  (hS : S.t₀ = t₀ ∧ S.x₀ = x₀)

include hMne hKne hT hlip hy hcont hm hiter hS

/-- Soundness of `ODE.half_line_refine`: the exact solution lies in the refined
interval at every grid point of `[t₀, T]`.

The upper end comes from the Euler bound alone; the lower end is the max of the Euler
lower end and the barrier `c`, which the solution respects by
`ODE.solution_half_line`. -/
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

/-- Soundness of `ODE.monotone_refine`: the exact solution lies in the refined interval
at every grid point of `[t₀, T]`.

Proved by induction on the step index. The inductive step needs both the Euler bound at
step `n + 1` and the monotonicity `y (t m) ≤ y (t (m+1))` supplied by
`ODE.solution_monotone`, which is what justifies carrying the running maximum of the
lower ends forward. -/
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

/-- Soundness of `ODE.lyapunov_refine`: the exact solution lies in the refined interval
at every grid point of `[t₀, T]`.

Both ends are tightened here: the Euler interval is intersected with the invariant band
`[-R, R]` furnished by `ODE.solution_lyapunov_kind`. -/
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

/-! ## The vector case

For a system, `ODE.euler_bound_solution_rational_vector` encloses the solution in a
*ball*: `‖y tₙ - xₙ‖ ≤ bound n`. Projecting that onto a coordinate
(`ODE.euler_bound_coord`, via `PiLp.norm_apply_le`) turns the ball into a box, after
which each coordinate can be refined exactly as in the scalar case, using the
coordinatewise rules of `DynaLean.Rules`:

* `half_space_refine_vector`, from `solution_half_space_vector`, sound by
  `half_space_bound_vector`;
* `monotone_refine_vector`, from `solution_monotone_vector`, sound by
  `monotone_bound_vector`;
* `lyapunov_refine_vector`, from `solution_lyapunov_kind_vector`, sound by
  `lyapunov_bound_vector`.

Projecting a ball to a box is lossy — a coordinate interval of half-width `bound n` is
all the ball gives, and the box it produces has circumradius `√k · bound n` — but it is
what makes the rules applicable at all, since the rules constrain coordinates. The
enclosure actually certified is the intersection of the ball with the refined box, and
both halves are available: `ODE.euler_bound_solution_rational_vector` for the ball and
the theorems below for the box. -/

/-- The vector analogue of `ODE.half_line_refine`, in coordinate `i`: intersect the
coordinate interval `xₙ i ± bound n` with the half-line `[c, ∞)`. -/
def half_space_refine_vector {k : ℕ} (S : VectorScheme k) (ε c K M : ℚ) (i : Fin k) (n : ℕ) :
    ℚ × ℚ :=
  let Ln := (S.x n) i - bound n ε K M S.δ
  let Un := (S.x n) i + bound n ε K M S.δ
  (max c Ln, Un)

/-- The vector analogue of `ODE.monotone_refine`, in coordinate `i`: the lower end never
decreases along the grid, because the coordinate itself never does. -/
def monotone_refine_vector {k : ℕ} (S : VectorScheme k) (ε K M : ℚ) (i : Fin k) (n : ℕ) :
    ℚ × ℚ :=
  let Ln := (S.x n) i - bound n ε K M S.δ
  let Un := (S.x n) i + bound n ε K M S.δ
  match n with
  | 0 => (Ln, Un)
  | m + 1 => (max (monotone_refine_vector S ε K M i m).1 Ln, Un)

/-- The vector analogue of `ODE.lyapunov_refine`, in coordinate `i`: intersect the
coordinate interval `xₙ i ± bound n` with the invariant band `[-R, R]`. -/
def lyapunov_refine_vector {k : ℕ} (S : VectorScheme k) (ε R K M : ℚ) (i : Fin k) (n : ℕ) :
    ℚ × ℚ :=
  let Ln := (S.x n) i - bound n ε K M S.δ
  let Un := (S.x n) i + bound n ε K M S.δ
  (max (-R) Ln, min R Un)

/-- Project the vector Euler bound onto a single coordinate.

`ODE.euler_bound_solution_rational_vector` bounds `‖y tₙ - xₙ‖`; since every coordinate
of a vector is bounded by its Euclidean norm (`PiLp.norm_apply_le`), the same number
bounds `|y tₙ i - xₙ i|` for each `i`. This is what converts the ball enclosure into a
box enclosure, and it is the only place where the vector refinements below touch the
Euler machinery. -/
theorem euler_bound_coord {k : ℕ} {f : ℝ → (ℝ^k) → ℝ^k} {y : ℝ → ℝ^k}
    {ε t₀ T K M : ℚ} {x₀ : ℚ^k} {S : VectorScheme k}
    (hMne : 0 < M) (hKne : 0 < K) (hT : t₀ < T)
    (hlip : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
    (hy : SolutionExistsVector f (x₀ : ℝ^k) y (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T))
    (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) T))
    (hm : ∀ (t : ℚ) (x : ℚ^k), ‖f t (x : ℝ^k) - S.m t x‖ ≤ ε)
    (hiter : ∀ t ∈ Set.Ioo (t₀ : ℝ) T, ‖iteratedDeriv 2 y t‖ ≤ M)
    (hS : S.t₀ = t₀ ∧ S.x₀ = x₀) (i : Fin k) :
    ∀ n ∈ Finset.range (⌊(T - t₀)/S.δ⌋₊ + 1),
      |y (S.t n) i - (((S.x n) i : ℚ) : ℝ)| ≤ ((bound n ε K M S.δ : ℚ) : ℝ) := by
  intro n hn
  have hrat := euler_bound_solution_rational_vector f x₀ t₀ T M hMne (by exact_mod_cast hKne)
    hy hcont S hT hm hlip hiter hS n hn
  have hproj : |y ((S.t n : ℚ) : ℝ) i - (((S.x n) i : ℚ) : ℝ)|
      ≤ ‖y ((S.t n : ℚ) : ℝ) - ((S.x n : ℚ^k) : ℝ^k)‖ := by
    have h := PiLp.norm_apply_le (y ((S.t n : ℚ) : ℝ) - ((S.x n : ℚ^k) : ℝ^k)) i
    rwa [Real.norm_eq_abs] at h
  refine hproj.trans (hrat.trans (le_of_eq ?_))
  simp only [bound]
  push_cast
  ring

/-- Grid points of a vector scheme anchored at `t₀` lie in `[t₀, T]`.

`VectorScheme.time_mem` phrased relative to the scheme's own `S.t₀`; this rewrites it
along `hS1 : S.t₀ = t₀` so it can be fed to the rules of `DynaLean.Rules`, whose
hypotheses are stated on `[t₀, T]`. -/
theorem vector_time_mem {k : ℕ} {t₀ T : ℚ} {S : VectorScheme k}
    (hT : t₀ < T) (hS1 : S.t₀ = t₀) {n : ℕ}
    (hn : n ∈ Finset.range (⌊(T - t₀) / S.δ⌋₊ + 1)) :
    ((S.t n : ℚ) : ℝ) ∈ Set.Icc ((t₀ : ℚ) : ℝ) ((T : ℚ) : ℝ) := by
  have hle : S.t₀ ≤ T := by rw [hS1]; exact hT.le
  have h := S.time_mem T hle n (by rw [hS1]; exact hn)
  rwa [hS1] at h

section VectorRefineProofs

/-! ### Soundness of the vector refinements

The hypothesis block mirrors the scalar one exactly, with `SolutionExists` replaced by
`SolutionExistsVector` and the absolute values by norms: these are the hypotheses of
`ODE.euler_bound_solution_rational_vector`, plus whatever the particular rule needs. -/

variable {k : ℕ} {f : ℝ → (ℝ^k) → ℝ^k} {y : ℝ → ℝ^k} {S : VectorScheme k}
  {ε t₀ T K M : ℚ} {x₀ : ℚ^k} (hMne : 0 < M) (hKne : 0 < K)
  (hT : t₀ < T)
  (hlip : ∀ t ∈ Set.Icc (t₀ : ℝ) T, LipschitzWith (K : ℝ).toNNReal (fun x => f t x))
  (hy : SolutionExistsVector f (x₀ : ℝ^k) y (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T))
  (hcont : ContDiffOn ℝ 2 y (Set.Icc (t₀ : ℝ) T))
  (hm : ∀ (t : ℚ) (x : ℚ^k), ‖f t (x : ℝ^k) - S.m t x‖ ≤ ε)
  (hiter : ∀ t ∈ Set.Ioo (t₀ : ℝ) T, ‖iteratedDeriv 2 y t‖ ≤ M)
  (hS : S.t₀ = t₀ ∧ S.x₀ = x₀)

include hMne hKne hT hlip hy hcont hm hiter hS

/-- Soundness of `ODE.half_space_refine_vector`: coordinate `i` of the exact solution
lies in the refined interval at every grid point of `[t₀, T]`.

The upper end comes from the projected Euler bound alone; the lower end is the max of
that bound's lower end and the barrier `c`, which the solution respects by
`ODE.solution_half_space_vector`. -/
theorem half_space_bound_vector (i : Fin k) (c : ℚ) (hc : (c : ℝ) ≤ y (t₀ : ℝ) i)
  (hfc : ∀ t ∈ Set.Icc (t₀ : ℝ) T, ∀ x : ℝ^k, x i ≤ (c : ℝ) → 0 ≤ (f t x) i)
  : ∀ n ∈ Finset.range (⌊(T - t₀)/ S.δ⌋₊ + 1),
    y (S.t n) i ∈ Set.Icc ((half_space_refine_vector S ε c K M i n).1 : ℝ)
                          ((half_space_refine_vector S ε c K M i n).2 : ℝ) :=
  by
  intro n hn
  have hco := euler_bound_coord hMne hKne hT hlip hy hcont hm hiter hS i n hn
  have hcomp := solution_half_space_vector i hy hc hfc
  have hmem := vector_time_mem hT hS.1 hn
  rw [abs_le] at hco
  obtain ⟨hco1, hco2⟩ := hco
  simp only [half_space_refine_vector, Set.mem_Icc]
  push_cast at hco1 hco2 ⊢
  exact ⟨max_le (hcomp _ hmem) (by linarith), by linarith⟩

/-- Soundness of `ODE.monotone_refine_vector`: coordinate `i` of the exact solution lies
in the refined interval at every grid point of `[t₀, T]`.

Proved by induction on the step index, exactly as in the scalar case. The inductive step
needs both the projected Euler bound at step `m + 1` and the monotonicity
`y (t m) i ≤ y (t (m+1)) i` supplied by `ODE.solution_monotone_vector`, which is what
justifies carrying the running maximum of the lower ends forward. -/
theorem monotone_bound_vector (i : Fin k)
  (hf : ∀ t ∈ Set.Icc (t₀ : ℝ) T, 0 ≤ (f t (y t)) i)
  : ∀ n ∈ Finset.range (⌊(T - t₀)/ S.δ⌋₊ + 1),
    y (S.t n) i ∈ Set.Icc ((monotone_refine_vector S ε K M i n).1 : ℝ)
                          ((monotone_refine_vector S ε K M i n).2 : ℝ) :=
  by
  have hmono := solution_monotone_vector i hy hf
  intro n
  induction n with
  | zero =>
    intro hn
    have hb : bound 0 ε K M S.δ = 0 := by simp [bound]
    have hx : y ((S.t 0 : ℚ) : ℝ) i = (((S.x 0) i : ℚ) : ℝ) := by
      rw [VectorScheme.t_zero, VectorScheme.x_zero, hS.1, hS.2, hy.1]
      rfl
    simp only [monotone_refine_vector, hb, sub_zero, add_zero, Set.mem_Icc, hx]
    exact ⟨le_rfl, le_rfl⟩
  | succ m ih =>
    intro hn
    have hmp : m ∈ Finset.range (⌊(T - t₀) / S.δ⌋₊ + 1) := by
      simp only [Finset.mem_range] at hn ⊢
      omega
    have ihm := ih hmp
    have hco := euler_bound_coord hMne hKne hT hlip hy hcont hm hiter hS i (m + 1) hn
    rw [abs_le] at hco
    obtain ⟨hco1, hco2⟩ := hco
    have hstep : y ((S.t m : ℚ) : ℝ) i ≤ y ((S.t (m + 1) : ℚ) : ℝ) i := by
      have hst : ((S.t m : ℚ) : ℝ) ≤ ((S.t (m + 1) : ℚ) : ℝ) := by
        have h : S.t m ≤ S.t (m + 1) := by
          rw [VectorScheme.t_succ]; linarith [S.hδ.le]
        exact_mod_cast h
      exact hmono (vector_time_mem hT hS.1 hmp) (vector_time_mem hT hS.1 hn) hst
    simp only [monotone_refine_vector, Set.mem_Icc]
    push_cast at hco1 hco2 ⊢
    exact ⟨max_le (le_trans ihm.1 hstep) (by linarith), by linarith⟩

/-- Soundness of `ODE.lyapunov_refine_vector`: coordinate `i` of the exact solution lies
in the refined interval at every grid point of `[t₀, T]`.

Both ends are tightened: the projected Euler interval is intersected with the invariant
band `[-R, R]` furnished by `ODE.solution_lyapunov_kind_vector`. -/
theorem lyapunov_bound_vector (i : Fin k) (R : ℚ)
  (hf : ∀ t ∈ Set.Icc (t₀ : ℝ) T, (∀ x : ℝ^k, (R : ℝ) ≤ x i → (f t x) i ≤ 0) ∧
    (∀ x : ℝ^k, x i ≤ (-R : ℝ) → 0 ≤ (f t x) i))
  (hs : y (t₀ : ℝ) i ∈ Set.Icc (-R : ℝ) (R : ℝ))
  : ∀ n ∈ Finset.range (⌊(T - t₀)/ S.δ⌋₊ + 1),
    y (S.t n) i ∈ Set.Icc ((lyapunov_refine_vector S ε R K M i n).1 : ℝ)
                          ((lyapunov_refine_vector S ε R K M i n).2 : ℝ) :=
  by
  intro n hn
  have hco := euler_bound_coord hMne hKne hT hlip hy hcont hm hiter hS i n hn
  have hcomp := solution_lyapunov_kind_vector i hy hf hs
  have hband := hcomp _ (vector_time_mem hT hS.1 hn)
  rw [abs_le] at hco
  obtain ⟨hco1, hco2⟩ := hco
  simp only [lyapunov_refine_vector, Set.mem_Icc]
  push_cast at hco1 hco2 ⊢
  exact ⟨max_le hband.1 (by linarith), le_min hband.2 (by linarith)⟩

end VectorRefineProofs

end ODE
