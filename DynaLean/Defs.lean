module

public import Mathlib
set_option linter.style.header false

/-! # Core definitions

The vocabulary shared by every other module in DynaLean:

* `ODE.SolutionExists` and `ODE.SolutionExistsVector` — what it means for a function to
  solve the initial value problem `x' = f t x`, `x t₀ = x₀`, in the scalar and the
  finite-dimensional case respectively;
* the notations `ℝ^n` and `ℚ^n` for `EuclideanSpace ℝ (Fin n)` and
  `EuclideanSpace ℚ (Fin n)`, together with the coercion `ℚ^n → ℝ^n`;
* `ODE.clamp` — nearest-point projection of a real number into an interval, and
  `ODE.clampBall` — its `ℝ^n` analogue, the nearest-point projection onto a closed ball;
* `ODE.extend` / `ODE.extendVector` — the constant extension of a (scalar, resp.
  vector-valued) field that is only meaningful on a compact box, used to turn local
  hypotheses into global ones.
-/

@[expose] public section

namespace ODE
section OneDDef
variable (f : ℝ → ℝ → ℝ) (x₀ : ℝ)

/-- A predicate expressing that `x` solves the ODE driven by `f` on an interval.

`SolutionExists f x₀ x t₀ t₁ s` says that `x t₀ = x₀` and that at every time of
`Icc t₀ t₁` the function `x` has derivative `f t (x t)` *within the set `s`*. Taking
`s = Set.Icc t₀ t₁` (as every downstream result does) gives the usual notion of a
solution on a closed interval, with one-sided derivatives at the endpoints. -/
def SolutionExists (x : ℝ → ℝ) (t₀ t₁ : ℝ) (s : Set ℝ) : Prop :=
  x t₀ = x₀ ∧ ∀ t ∈ Set.Icc t₀ t₁, HasDerivWithinAt x (f t (x t)) s t
end OneDDef

section nDDef
open Lean Meta Elab Term

/-! ## Notation for finite-dimensional state spaces

`ℝ^n` and `ℚ^n` elaborate to `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℚ (Fin n)`,
i.e. `Fin n → ℝ` (resp. `Fin n → ℚ`) carried with the `L²` norm. The `atomic` prefix
makes the parser commit to the notation as soon as it sees `ℝ^`, so that `ℝ^n` is never
mistaken for a power of a real number. -/

/-- `ℝ^n` denotes `EuclideanSpace ℝ (Fin n)`: the `L²`-normed space of `n` reals. -/
syntax atomic("ℝ^"term) : term
/-- `ℚ^n` denotes `EuclideanSpace ℚ (Fin n)`: the exactly representable state vectors
used by the numerical schemes. -/
syntax atomic("ℚ^"term) : term

-- Elaborator for the `ℝ^n` and `ℚ^n` notations declared just above: elaborate the
-- exponent as a `ℕ`, build `Fin n`, and wrap it in `EuclideanSpace`.
elab_rules : term
  | `(term| ℝ^$n) => do
  let n ← elabTerm n none
  let t ← mkAppM ``Fin #[n]
  Term.synthesizeSyntheticMVarsNoPostponing
  let t ← mkAppM ``EuclideanSpace #[mkConst ``Real , t]
  return t
  | `(term| ℚ^$n) => do
  let n ← elabTerm n none
  let t ← mkAppM ``Fin #[n]
  Term.synthesizeSyntheticMVarsNoPostponing
  let t ← mkAppM ``EuclideanSpace #[mkConst ``Rat , t]
  return t



/-- Coerce a rational state vector to a real one, coordinatewise.

This is what lets a numerical scheme (which lives in `ℚ^n`, so that its iterates are
exact and computable) be compared with an analytic solution (which lives in `ℝ^n`). -/
instance {n : ℕ} : Coe (ℚ^n) (ℝ^n) where
  coe := fun x => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => (x i : ℝ))

/-- The vector-valued analogue of `ODE.SolutionExists`.

`SolutionExistsVector f x₀ x t₀ t₁ s` says that `x t₀ = x₀` and that at every time of
`Icc t₀ t₁` the curve `x : ℝ → ℝ^n` has derivative `f t (x t)` within `s`. The
derivative is the `HasDerivWithinAt` of a curve, so it is a vector in `ℝ^n`. -/
def SolutionExistsVector {n : ℕ} (f : ℝ → (ℝ^n) → ℝ^n) (x₀ : ℝ^n)
 (x : ℝ → ℝ^n) (t₀ t₁ : ℝ) (s : Set ℝ) : Prop :=
  x t₀ = x₀ ∧ ∀ t ∈ Set.Icc t₀ t₁, HasDerivWithinAt x (f t (x t)) s t


end nDDef

/-! ## Clamping a real number into an interval -/

/-- Clamp `y` into `[a, b]`: the nearest-point projection when `a ≤ b`. -/
noncomputable def clamp (a b y : ℝ) : ℝ := max a (min b y)

/-- The clamped value lies in the target interval. -/
theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (y : ℝ) : clamp a b y ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- Clamping leaves values already in the interval unchanged. -/
theorem clamp_eq_self {a b y : ℝ} (hy : y ∈ Set.Icc a b) : clamp a b y = y := by
  rw [clamp, min_eq_right hy.2, max_eq_right hy.1]

/-- Clamping is nonexpansive, hence Lipschitz with constant `1`. -/
theorem lipschitzWith_clamp (a b : ℝ) : LipschitzWith 1 (clamp a b) :=
  (LipschitzWith.id.const_min b).const_max a

/-! ## Clamping a vector into a closed ball

The `ℝ^n` analogue of `ODE.clamp`. In dimension one the interval `Icc (c - r) (c + r)` *is*
the closed ball `closedBall c r`, and `clampBall` is the radial retraction that reduces to
`clamp` there: it fixes the points of the ball and pushes everything else onto its
boundary along the ray from the centre. -/

section ClampBall

open scoped InnerProductSpace

variable {n : ℕ}

/-- Clamp `y` into `closedBall c r`: the nearest-point projection when `0 ≤ r`.

The point is left untouched when `‖y - c‖ ≤ r`; otherwise it is moved to the point where
the ray from `c` through `y` meets the sphere of radius `r`. -/
noncomputable def clampBall (c : ℝ^n) (r : ℝ) (y : ℝ^n) : ℝ^n :=
  c + (min 1 (r / ‖y - c‖)) • (y - c)

/-- The clamped vector lies in the target ball. -/
theorem clampBall_mem {c : ℝ^n} {r : ℝ} (hr : 0 ≤ r) (y : ℝ^n) :
    clampBall c r y ∈ Metric.closedBall c r := by
  have hs : (0 : ℝ) ≤ ‖y - c‖ := norm_nonneg _
  rw [Metric.mem_closedBall, dist_eq_norm, clampBall, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs]
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, mul_zero]; exact hr
  · have h0 : 0 ≤ min 1 (r / ‖y - c‖) := le_min zero_le_one (div_nonneg hr hs)
    rw [abs_of_nonneg h0]
    calc min 1 (r / ‖y - c‖) * ‖y - c‖ ≤ (r / ‖y - c‖) * ‖y - c‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hs
      _ = r := by field_simp

/-- Clamping leaves vectors already in the ball unchanged. -/
theorem clampBall_eq_self {c : ℝ^n} {r : ℝ} {y : ℝ^n} (hy : y ∈ Metric.closedBall c r) :
    clampBall c r y = y := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  rcases eq_or_lt_of_le (norm_nonneg (y - c)) with h | h
  · have hyc : y = c := by rw [← norm_sub_eq_zero_iff]; exact h.symm
    rw [clampBall, hyc]; simp
  · rw [clampBall, min_eq_left ((one_le_div h).mpr hy), one_smul]; abel

/-- Clamping into a ball is nonexpansive, hence Lipschitz with constant `1`.

The `ℝ^n` analogue of `ODE.lipschitzWith_clamp`, but without a coordinatewise proof
available: `‖·‖²` is expanded through the inner product and the three possible positions
of the pair `(y, z)` relative to the ball are treated separately. The case where both
points sit outside is where the Euclidean (rather than merely normed) structure is used. -/
theorem lipschitzWith_clampBall (c : ℝ^n) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith 1 (clampBall c r) := by
  -- The scaling factor is the identity inside the ball, and `r / ‖u‖` outside it.
  have hin : ∀ u : ℝ^n, ‖u‖ ≤ r → (min 1 (r / ‖u‖)) • u = u := by
    intro u hu
    rcases eq_or_lt_of_le (norm_nonneg u) with h | h
    · have hu0 : u = 0 := by rw [← norm_eq_zero]; exact h.symm
      rw [hu0, smul_zero]
    · rw [min_eq_left ((one_le_div h).mpr hu), one_smul]
  have hout : ∀ u : ℝ^n, r < ‖u‖ → (min 1 (r / ‖u‖)) • u = (r / ‖u‖) • u := by
    intro u hu
    rw [min_eq_right ((div_le_one (lt_of_le_of_lt hr hu)).mpr hu.le)]
  -- One point inside the ball, one outside: `⟪v, w⟫ ≤ ‖v‖ * ‖w‖ ≤ r * ‖w‖` does it.
  have mixed : ∀ v w : ℝ^n, ‖v‖ ≤ r → r < ‖w‖ → ‖v - (r / ‖w‖) • w‖ ≤ ‖v - w‖ := by
    intro v w hv hw
    have hb : 0 < ‖w‖ := lt_of_le_of_lt hr hw
    set s : ℝ := r / ‖w‖ with hsdef
    have hs0 : 0 ≤ s := div_nonneg hr hb.le
    have hs1 : s ≤ 1 := (div_le_one hb).mpr hw.le
    have hsb : s * ‖w‖ = r := by rw [hsdef]; field_simp
    have hvw : ⟪v, w⟫_ℝ ≤ s * ‖w‖ ^ 2 := by
      have h1 := real_inner_le_norm v w
      have h2 : ‖v‖ * ‖w‖ ≤ r * ‖w‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg w)
      have h3 : r * ‖w‖ = s * ‖w‖ ^ 2 := by rw [← hsb]; ring
      linarith
    have e1 : ‖v - s • w‖ ^ 2 = ‖v‖ ^ 2 - 2 * s * ⟪v, w⟫_ℝ + s ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs0]
      ring
    have e2 : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * ⟪v, w⟫_ℝ + ‖w‖ ^ 2 := norm_sub_sq_real v w
    have hsq : ‖v - s • w‖ ^ 2 ≤ ‖v - w‖ ^ 2 := by
      rw [e1, e2]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hvw),
        mul_nonneg (sq_nonneg (1 - s)) (sq_nonneg ‖w‖)]
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  -- Both points outside: the difference of the two squared norms is `(‖v‖ - ‖w‖) ^ 2`
  -- once the scalings are accounted for.
  have outout : ∀ v w : ℝ^n, r < ‖v‖ → r < ‖w‖ →
      ‖(r / ‖v‖) • v - (r / ‖w‖) • w‖ ≤ ‖v - w‖ := by
    intro v w hv hw
    have ha : 0 < ‖v‖ := lt_of_le_of_lt hr hv
    have hb : 0 < ‖w‖ := lt_of_le_of_lt hr hw
    set p : ℝ := r / ‖v‖ with hpdef
    set q : ℝ := r / ‖w‖ with hqdef
    have hp0 : 0 ≤ p := div_nonneg hr ha.le
    have hq0 : 0 ≤ q := div_nonneg hr hb.le
    have hp1 : p ≤ 1 := (div_le_one ha).mpr hv.le
    have hq1 : q ≤ 1 := (div_le_one hb).mpr hw.le
    have hpa : p * ‖v‖ = r := by rw [hpdef]; field_simp
    have hqb : q * ‖w‖ = r := by rw [hqdef]; field_simp
    have hpq : p * q ≤ 1 := by nlinarith
    have hzero : (p * ‖v‖ - q * ‖w‖) ^ 2 = 0 := by rw [hpa, hqb]; ring
    have hvw : ⟪v, w⟫_ℝ ≤ ‖v‖ * ‖w‖ := real_inner_le_norm v w
    have e1 : ‖p • v - q • w‖ ^ 2
        = p ^ 2 * ‖v‖ ^ 2 - 2 * (p * q) * ⟪v, w⟫_ℝ + q ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0, abs_of_nonneg hq0]
      ring
    have e2 : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * ⟪v, w⟫_ℝ + ‖w‖ ^ 2 := norm_sub_sq_real v w
    have hsq : ‖p • v - q • w‖ ^ 2 ≤ ‖v - w‖ ^ 2 := by
      rw [e1, e2]
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hvw),
        sq_nonneg (‖v‖ - ‖w‖), hzero]
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  -- The three cases assembled, after translating the centre to the origin.
  have core : ∀ v w : ℝ^n,
      ‖(min 1 (r / ‖v‖)) • v - (min 1 (r / ‖w‖)) • w‖ ≤ ‖v - w‖ := by
    intro v w
    rcases le_or_gt ‖v‖ r with hv | hv <;> rcases le_or_gt ‖w‖ r with hw | hw
    · rw [hin v hv, hin w hw]
    · rw [hin v hv, hout w hw]
      exact mixed v w hv hw
    · rw [hout v hv, hin w hw, norm_sub_rev, norm_sub_rev v w]
      exact mixed w v hw hv
    · rw [hout v hv, hout w hw]
      exact outout v w hv hw
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have hyz : clampBall c r y - clampBall c r z
      = (min 1 (r / ‖y - c‖)) • (y - c) - (min 1 (r / ‖z - c‖)) • (z - c) := by
    simp only [clampBall]
    abel
  have hsub : y - z = (y - c) - (z - c) := by abel
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, hyz, hsub]
  exact core (y - c) (z - c)

end ClampBall

/-! ## The constant extension of a locally defined vector field -/

/-- Extend `f`, a priori only meaningful on `Icc t₀ T ×ˢ closedBall c r`, to all of `ℝ × ℝ`
by clamping both arguments into that box.  The extension is constant in each direction
outside the box, and agrees with `f` on it. -/
noncomputable def extend (f : ℝ → ℝ → ℝ) (t₀ T c r : ℝ) : ℝ → ℝ → ℝ :=
  fun t y => f (clamp t₀ T t) (clamp (c - r) (c + r) y)

/-- The `ℝ^n` analogue of `ODE.extend`.

Extend `f`, a priori only meaningful on `Icc t₀ T ×ˢ closedBall c r`, to all of `ℝ × ℝ^n`
by clamping the time into the interval and the state into the ball.  The extension agrees
with `f` on the box, and is constant along each ray leaving it. -/
noncomputable def extendVector {n : ℕ} (f : ℝ → (ℝ^n) → ℝ^n) (t₀ T : ℝ) (c : ℝ^n) (r : ℝ) :
    ℝ → (ℝ^n) → ℝ^n :=
  fun t y => f (clamp t₀ T t) (clampBall c r y)

end ODE
