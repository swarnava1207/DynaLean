module

public import DynaLean.Defs
public import DynaLean.EulerScheme
public import DynaLean.EulerBound

@[expose] public section

/-! # Digital twins: definitions

A *digital twin* here is a physical system `z` that is being tracked by a model. Three
things are being distinguished, and keeping them apart is the whole point:

* `z` — the real trajectory. Unknown; it solves `z' = g t z` for some true but unknown
  field `g`.
* `f` — the modelled field, which is known and analytic, and which is only required to
  agree with reality to within `εz` *inside the operating region* `Ω`.
* `m` — the rational model field actually iterated by the numerical scheme, which is
  only required to agree with `f` to within `εm`.

So two separate error budgets enter: `εz` for model-versus-reality, and `εm` (together
with the Euler constants `K` and `M`) for scheme-versus-model. The first is packaged by
`ODE.DigitalTwin`, the second by `ODE.EB` and `ODE.SegmentCert`.

## Measurements and the tube

The twin is re-anchored by *measurements*: at scheduled times the state is observed to
lie in an axis-aligned box. `Schedule` carries that data — the measurement times `τ`,
the per-coordinate box bounds `A`/`B` (each bound optional, so a coordinate may be
unmeasured in either direction), and how many Euler steps to take on each segment.

The reachable set is then propagated as a sequence of balls, one per measurement node:

* `ODE.Rec` intersects the current ball with the measured box and re-centres, shrinking
  the radius when the intersection permits and returning `none` when the two are
  disjoint — i.e. when no trajectory can explain the measurements;
* `ODE.segEnd` pushes a ball across one segment, growing its radius by `εz · h` of
  model drift plus `ODE.EB` of Euler error;
* `ODE.nodeAt` alternates the two along the schedule, and `ODE.BuildTube` returns the
  final node (or `none`);
* `ODE.segCentre` and `ODE.segRadius` describe the resulting tube at *every* time, not
  just at nodes.

The soundness theorems for all of this live in `DynaLean.DigitalTwin.MemBox`.
-/

namespace ODE

/-- The hypotheses making `z` a digital twin of the model field `f` on `[t₀, T]`.

`z` is an unknown true trajectory: it solves `z' = g t z` for the unknown field `g`,
stays inside the operating region `Ω`, and — this is the substantive assumption — the
modelled field `f` evaluated anywhere in `Ω` differs from the realized velocity
`g t (z t)` by at most `εz`.

Note how weak that last condition is: nothing is assumed about `g` away from the actual
trajectory, so `g` never has to be known. -/
structure DigitalTwin {k : ℕ} (z : ℝ → ℝ^k)
  (f g : ℝ → (ℝ^k) → ℝ^k) (Ω : Set (ℝ × ℝ^k))
  (εz : ℚ) (t₀ T : ℚ) where
  /-- The (unknown) true initial state. -/
  z₀ : ℝ^k
  /-- `z` solves the true dynamics `z' = g t z` from `z₀` on `[t₀, T]`. -/
  hz : SolutionExistsVector g z₀ z (t₀ : ℝ) T (Set.Icc (t₀ : ℝ) T)
  /-- The true trajectory never leaves the operating region `Ω`. -/
  hzΩ : ∀ t ∈ Set.Icc (t₀ : ℝ) T, (t, z t) ∈ Ω
  /-- Model fidelity: inside `Ω`, the modelled field is within `εz` of the velocity
  actually realized by the true trajectory. -/
  hfg : ∀ t ∈ Set.Icc (t₀ : ℝ) T, ∀ x : ℝ^k, (t, x) ∈ Ω →
          ‖f t x - g t (z t)‖ ≤ (εz : ℝ)

section MemBox

/-- `MemBox x A B`: the state `x` lies in the axis-aligned box with optional lower
bounds `A` and optional upper bounds `B`.

Each coordinate may be bounded below, above, both or neither, which is what lets a
single predicate describe a partial measurement — a sensor that reads only some
coordinates, or only one side of them. -/
def MemBox {k : ℕ} (x : ℝ^k) (A B : Fin k → Option ℚ) : Prop :=
  ∀ i : Fin k,
  match A i, B i with
  | some a, some b => (a ≤ x i) ∧ (x i ≤ b)
  | some a, none => a ≤ x i
  | none, some b => x i ≤ b
  | none, none => True

/-- A measurement schedule on `[t₀, T]` for a `k`-dimensional system.

The interval is cut into `p` segments by the strictly increasing times
`τ 0 = t₀ < τ 1 < … < τ p = T`. At each of the `p + 1` nodes a (possibly partial) box
measurement `A i`/`B i` is available, and on each of the `p` segments the scheme takes
`N i` Euler steps. -/
structure Schedule (k : ℕ) (t₀ T : ℚ) where
  /-- The number of segments; `p + 1` is the number of measurement nodes. -/
  p : ℕ
  /-- There is at least one segment. -/
  hp : p ≠ 0
  /-- The measurement times. -/
  τ  : Fin (p+1) → ℚ
  /-- The measurement times are strictly increasing, so the segments are nondegenerate. -/
  hmono  : StrictMono τ
  /-- The first measurement is at the initial time. -/
  hfirst : τ 0 = t₀
  /-- The last measurement is at the final time. -/
  hlast  : τ (Fin.last p) = T
  /-- Per-node, per-coordinate optional lower bounds of the measured box. -/
  A : Fin (p + 1) → Fin k → Option ℚ
  /-- Per-node, per-coordinate optional upper bounds of the measured box. -/
  B : Fin (p + 1) → Fin k → Option ℚ
  /-- The number of Euler steps to take on each segment. -/
  N : Fin p → ℕ
  /-- Every segment takes at least one step, so `δ` below is well defined. -/
  hN : ∀ i, N i ≠ 0

namespace Schedule
variable {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)

/-- The length `τ (i+1) - τ i` of segment `i`. -/
def h (i : Fin sch.p) : ℚ := sch.τ (i.succ) - sch.τ i.castSucc

/-- The Euler step size on segment `i`: its length divided by its step count. -/
def δ (i : Fin sch.p) : ℚ := sch.h i / (sch.N i : ℚ)

/-- The `n`-th grid time inside segment `i`, i.e. `τ i + n · δ i`. -/
def s (i : Fin sch.p) (n : ℕ) : ℚ := sch.τ i.castSucc + n * sch.δ i

/-- Segments have positive length, because the measurement times strictly increase. -/
theorem h_pos (i : Fin sch.p) : 0 < sch.h i := sub_pos.mpr (sch.hmono (Fin.castSucc_lt_succ))

/-- Step sizes are positive: a positive segment length divided by a nonzero step
count. -/
theorem δ_pos (i : Fin sch.p) : 0 < sch.δ i := by
  simp only [δ, sch.h_pos i, div_pos_iff_of_pos_left, Nat.cast_pos]
  apply Nat.pos_of_ne_zero (sch.hN i)

/-- The grid of segment `i` starts at the left measurement time `τ i`. -/
theorem s_zero (i : Fin sch.p) : sch.s i 0 = sch.τ i.castSucc := by
  simp only [s, CharP.cast_eq_zero, zero_mul, add_zero]

/-- The grid of segment `i` ends exactly at the right measurement time `τ (i+1)`: the
`N i` steps of size `δ i` fit the segment with no remainder. -/
theorem s_last (i : Fin sch.p) : sch.s i (sch.N i) = sch.τ (i.succ) := by
  simp only [s, δ]
  rw [IsUnit.mul_div_cancel _ (sch.h i)]
  · simp only [h, add_sub_cancel]
  · simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero]
    exact (sch.hN i)
end Schedule

/-- `MeasuredBy z sch`: the trajectory `z` is consistent with every measurement in the
schedule, i.e. at each node `τ i` it lies in the box `(A i, B i)`.

This is the observational input to the whole method: it is what the sensors assert. -/
def MeasuredBy {k : ℕ} {t₀ T : ℚ} (z : ℝ → ℝ^k) (sch : Schedule k t₀ T) : Prop :=
  ∀ i : Fin (sch.p + 1), MemBox (z (sch.τ i)) (sch.A i) (sch.B i)

/-- A rational upper bound for `√x`, computed exactly.

Writing `x = p / q` with `p = x.num`, `q = x.den`, this returns
`(⌊√(p·q)⌋ + 1) / q`, which is `≥ √x` by `ODE.le_sq_sqrtUB`. Rational arithmetic cannot
represent `√x` itself, so every radius computation in this development rounds *upward*
through this function, keeping the enclosures sound. -/
def sqrtUB (x : ℚ) : ℚ := (Nat.sqrt (x.num.toNat * x.den) + 1) / x.den

/-- A rational upper bound for the Euclidean norm of a rational vector: `sqrtUB`
applied to the sum of squares. See `ODE.norm_le_qnormUB`. -/
def qnormUB {k : ℕ} (x : ℚ^k) : ℚ := sqrtUB (∑ i : Fin k, (x i) ^ 2)

/-- Coordinatewise intersection of the ball `closedBall c r` with the measured box
`(A, B)`, returned as the list of `(lower, upper)` pairs.

Each coordinate contributes `[cᵢ - r, cᵢ + r]` clipped by whichever of the measured
bounds is present. A pair with `lower > upper` signals that the intersection is empty
in that coordinate; `ODE.Rec` checks for exactly that. -/
def ObtainLU {k : ℕ} (c : ℚ^k) (r : ℚ) (A B : Fin k → Option ℚ) : List (ℚ × ℚ) :=
  List.ofFn fun i : Fin k =>
    ( match A i with | some a => max a (c.ofLp i - r) | none => c.ofLp i - r,
      match B i with | some b => min b (c.ofLp i + r) | none => c.ofLp i + r )

/-- Re-centre the ball `closedBall c r` on a measurement.

Intersects the ball with the measured box (`ODE.ObtainLU`) and then:

* if some coordinate interval is empty, returns `none` — no state can satisfy both the
  prior ball and the measurement, which `ODE.rec_refute` turns into a refutation;
* otherwise computes the box's circumradius `rbox`; if `rbox ≤ r` the box is strictly
  better than the prior ball, so the new enclosure is the ball around the box's centre
  with radius `rbox`; if not, the measurement is uninformative and `(c, r)` is kept.

Soundness is `ODE.rec_sound`: anything in the old ball *and* in the box is in the new
ball. -/
def Rec {k : ℕ} (c : ℚ^k) (r : ℚ) (A B : Fin k → (Option ℚ)) : Option ((ℚ^k) × ℚ) :=
  let LU := ObtainLU c r A B
  if LU.all (fun (l, u) => l ≤ u) then
    let rbox := sqrtUB ((LU.map (fun (l, u) => ((u - l) / 2) ^ 2)).sum)
    if rbox ≤ r then
      some ((WithLp.equiv 2 (Fin k → ℚ)).symm (fun i => (LU[i]!.1 + LU[i]!.2) / 2), rbox)
    else
      some (c, r)
  else
    none

/-- The Euler error budget after `n` steps: `(ε + M δ / 2) · ((1 + K δ)ⁿ - 1) / K`.

The same quantity as the right-hand side of
`ODE.euler_bound_solution_rational_vector`, with the `δ` in numerator and denominator
cancelled. Rational, hence exactly computable, which is what lets `ODE.BuildTube` run
as an ordinary program. -/
def EB (K ε M δ : ℚ) (n : ℕ) := (ε + M*δ/2) * ((1 + K*δ)^n - 1) / K

/-- A node of the propagated tube: a ball, given by its rational centre and radius. -/
abbrev Node (k : ℕ) := (ℚ^k) × ℚ

/-- Push an enclosing ball across one segment of the schedule.

Starting from `closedBall c r` at the left end of segment `i`, runs `N i` Euler steps
of the model field `m` (via `ODE.LastVectorSchema`, so the grid lands exactly on the
right measurement time) and returns the resulting ball. The radius grows by two
independent amounts:

* `εz · h i` — the model-versus-reality drift accumulated over the segment, by
  `ODE.bound_twin_shift`;
* `EB K εm M (δ i) (N i)` — the scheme-versus-model Euler error, by
  `ODE.euler_bound_solution_all_vector`. -/
def segEnd {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (εz εm K M : ℚ) (i : Fin sch.p) (c : ℚ^k) (r : ℚ) : Node k :=
  let S := LastVectorSchema (sch.τ i.castSucc) (sch.τ (i.succ)) c m (sch.N i) (sch.hN i)
    (sch.hmono (Fin.castSucc_lt_succ))
  (S.x (sch.N i), r + εz * (sch.h i) + EB K εm M (sch.δ i) (sch.N i))

/-- The enclosing ball at measurement node `i`, or `none` if the run has already been
refuted.

Defined by induction along the schedule: start from the prior `closedBall x₀ ρ₀`
re-centred on the first measurement, then alternate `ODE.segEnd` (propagate across a
segment) with `ODE.Rec` (re-centre on the next measurement). The `Option` monad
short-circuits: once some `Rec` reports an empty intersection, every later node is
`none`.

Soundness is `ODE.node_invariant`; the refutation case is `ODE.drift_sound`. -/
def nodeAt {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (x₀ : ℚ^k) (ρ₀ εz εm K M : ℚ) : Fin (sch.p + 1) → Option (Node k) :=
  Fin.induction (motive := fun _ => Option (Node k))
    (Rec x₀ ρ₀ (sch.A 0) (sch.B 0))
    (fun i prev => do
      let (c, ρ) ← prev
      let (cE, rE) := segEnd sch m εz εm K M i c ρ
      Rec cE rE (sch.A i.succ) (sch.B i.succ))

/-- Run the whole schedule and return the final enclosing ball, or `none`.

`none` means the measurements are jointly inconsistent with the model and its error
budgets — by `ODE.drift_sound`, *no* digital twin satisfying the stated hypotheses can
produce those readings, which is the module's detection criterion for a drifted or
faulty model. -/
def BuildTube {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (x₀ : ℚ^k) (ρ₀ εz εm K M : ℚ) : Option (Node k) :=
  nodeAt sch m x₀ ρ₀ εz εm K M (Fin.last sch.p)

/-- The first measurement node at which the run fails, if any.

Diagnostic companion to `ODE.BuildTube`: where `BuildTube` only reports *that* the
measurements are inconsistent, this reports *when* the contradiction first appears. -/
def driftIndex {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T) (m : ℚ → (ℚ^k) → ℚ^k)
    (x₀ : ℚ^k) (ρ₀ εz εm K M : ℚ) : Option (Fin (sch.p + 1)) :=
  (List.finRange (sch.p + 1)).find? fun i => (nodeAt sch m x₀ ρ₀ εz εm K M i).isNone

/-- The centre of the tube at time `t` within segment `i`: the Euler interpolant of the
segment's scheme, started from the node centre `c`.

Together with `ODE.segRadius` this describes the enclosure at *every* time, not only at
the measurement nodes; see `ODE.tube_enclosure`. -/
noncomputable def segCentre {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)
    (m : ℚ → (ℚ^k) → ℚ^k) (i : Fin sch.p) (c : ℚ^k) (t : ℝ) : ℝ^k :=
  (LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) c m (sch.N i) (sch.hN i)
     (sch.hmono (Fin.castSucc_lt_succ))).plR t

/-- The radius of the tube at time `t` within segment `i`.

Three terms: the radius `ρ` inherited from the node at the left of the segment, the
model drift `εz · (t - τ i)` accumulated since then, and the segment's whole Euler
budget `EB K εm M (δ i) (N i)`. Note the drift term grows continuously in `t` while the
Euler term is charged in full from the start — the latter is a bound for the segment,
not a running total. -/
noncomputable def segRadius {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)
    (εz εm K M : ℚ) (i : Fin sch.p) (ρ : ℚ) (t : ℝ) : ℝ :=
  (ρ : ℝ) + (εz : ℝ) * (t - (sch.τ i.castSucc : ℝ)) + (EB K εm M (sch.δ i) (sch.N i) : ℝ)

/-- A certificate for one segment: everything the twin argument needs to know about
the *model* on segment `i`, starting from centre `c`.

Bundling it as a structure keeps the soundness proofs free of analysis. The caller is
expected to build a `SegmentCert` once per segment, discharging `hy` with the existence
results of `DynaLean.Existence` and `hEB` with
`ODE.euler_bound_solution_all_vector`; the theorems in `DynaLean.DigitalTwin.MemBox`
then only ever use it abstractly. -/
structure SegmentCert {k : ℕ} {t₀ T : ℚ} (sch : Schedule k t₀ T)
    (f : ℝ → (ℝ^k) → ℝ^k) (m : ℚ → (ℚ^k) → ℚ^k) (Ω : Set (ℝ × ℝ^k))
    (εm K M : ℚ) (i : Fin sch.p) (c : ℚ^k) where
  /-- The exact solution of the *model* field `f` on this segment. -/
  y : ℝ → ℝ^k
  /-- `y` solves `y' = f t y` on the segment, starting from the node centre `c`. -/
  hy : SolutionExistsVector f (c : ℝ^k) y (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ)
        (Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ))
  /-- The model solution stays in the operating region, so `DigitalTwin.hfg` applies
  along it. -/
  hyΩ : ∀ s ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ), (s, y s) ∈ Ω
  /-- The Euler interpolant for this segment tracks `y` to within the budget
  `EB K εm M (δ i) (N i)`, at every time of the segment. -/
  hEB : ∀ t ∈ Set.Icc (sch.τ i.castSucc : ℝ) (sch.τ i.succ : ℝ),
           (let S := LastVectorSchema (sch.τ i.castSucc) (sch.τ i.succ) c m (sch.N i) (sch.hN i)
                       (sch.hmono (Fin.castSucc_lt_succ))
            ‖y t - S.plR t‖ ≤ (EB K εm M (sch.δ i) (sch.N i) : ℝ))

end MemBox

end ODE
