# DynaLean

DynaLean is a Lean 4 formalization of elementary results for ordinary
differential equations and numerical Euler schemes. It builds on
[Mathlib](https://github.com/leanprover-community/mathlib4) for analysis,
integration, derivatives, and inequalities.

The library has two layers that meet in the middle:

- an **analytic layer** — existence, uniqueness, comparison, and a priori bounds
	for solutions of `x' = f (t, x)`;
- a **computational layer** — Euler schemes over `ℚ`, error bounds that are
	themselves rational (hence exactly evaluable), and metaprograms that turn a
	numerical computation into a kernel-checked theorem.

The bridge between them is `DynaLean/EulerBound.lean`, which bounds the distance
between an exact real solution and the rational data produced by a scheme.

## Contents

### Foundations

- `DynaLean/Basic.lean`: a minimal declaration, used to check that the toolchain
	and the Mathlib dependency are wired up correctly.
- `DynaLean/Defs.lean`: the `ODE.SolutionExists` and `ODE.SolutionExistsVector`
	predicates, the `ℝ^n` / `ℚ^n` notations and the coercion `ℚ^n → ℝ^n`, interval
	clamping (`ODE.clamp`), and the constant extension `ODE.extend` of a vector
	field defined only on a compact box.

### Analytic theory

- `DynaLean/Existence.lean`: restriction and gluing of solutions, stepwise
	existence, Picard-Lindelof-based existence by induction, uniqueness, and
	existence for a vector field defined on a compact box. Scalar and `ℝ^n`-valued
	versions.
- `DynaLean/Bounds.lean`: constant and time-dependent upper bounds for ODE
	solutions.
- `DynaLean/Comparison.lean`: first-order comparison of two ODE solutions, the
	workhorse behind uniqueness and the qualitative rules.
- `DynaLean/Bihari.lean`: a Bihari-type integral bound for nonnegative solutions
	— the nonlinear generalization of Grönwall's inequality.
- `DynaLean/Derivations.lean`: regularity of solutions. Promotes a `C¹`
	hypothesis on the vector field to `C²` for the solution, and bounds `‖y''‖` on
	a compact interval. This is what supplies the constant `M` that the Euler
	error bounds require.

### Euler schemes and their error

- `DynaLean/EulerScheme.lean`: the `Scheme` and `VectorScheme n` structures —
	rational Euler grids, iterates, and the piecewise-linear interpolant, together
	with their basic rewriting lemmas. Everything is rational, so the iterates are
	exactly computable.
- `DynaLean/EulerBound.lean`: Taylor estimates and global error bounds for the
	Euler scheme. Includes the one-step recurrence, its sharp solution by discrete
	Grönwall (rational, no `exp`), the extension from grid points to every time in
	the interval, and a specialization whose final grid point is exactly `T`.
	Scalar and `ℝ^k`-valued versions.

### Refining an estimate with prior knowledge

- `DynaLean/Rules.lean`: qualitative invariants a solution satisfies for
	structural reasons — an invariant half-line, monotonicity, and forward
	invariance of a band `[-R, R]` for an inward-pointing field. Each has an
	`ℝ^n`-valued counterpart stated in a single coordinate (half-space,
	coordinate monotonicity, invariant slab), plus `ODE.solution_mem_box_vector`:
	forward invariance of an axis-aligned box. The vector versions are proved
	from two reusable barrier lemmas for a real function with a prescribed
	derivative, rather than through the comparison theorem, so they need no
	Lipschitz hypothesis — at the cost of assuming the sign condition on a whole
	region rather than only on the boundary.
- `DynaLean/RulesBound.lean`: intersects each rule from `Rules.lean` with the
	Euler error interval, giving enclosures strictly tighter than either source
	alone. The vector half first projects the ball enclosure
	`‖y tₙ - xₙ‖ ≤ bound n` onto a coordinate (`ODE.euler_bound_coord`), turning
	it into a box, and then refines each coordinate as in the scalar case.
- `DynaLean/Refinement.lean`: the generic version. Prior one-sided bounds are
	modelled as `Option ℚ` (so "no information" is a first-class case), and
	`ODE.refinement` returns the midpoint of the Euler interval clipped by them,
	with the same error radius. Also includes a monotone variant.

### Metaprogramming: computations that produce theorems

- `DynaLean/Concrete.lean`: the `#derive_bound` command. Evaluates an iterate
	`S.x n` exactly, emits either `S.x n = v` or an outward-rounded two-sided
	bound, elaborates the candidate theorem so its proof is actually checked, and
	offers the result as a `Try this` suggestion.
- `DynaLean/MakeProof.lean`: proof *building* rather than proof search. The
	inductive predicates `HasBound` / `HasBoundVec` mirror the Euler recursion, so
	an enclosure after `n` steps is a chain of `n` constructor applications. On top
	sit the tactics `apply_bound` / `apply_bound_vec` and the command
	`#make_proof`, which generates and elaborates a pair of named theorems.
	This scales to step counts where asking a tactic to evaluate the iterate from
	scratch does not.

### Digital twins

- `DynaLean/DigitalTwin/Defs.lean`: definitions. A `DigitalTwin` is an unknown
	true trajectory `z` whose velocity is tracked by a known model field `f` to
	within `εz`, inside an operating region `Ω`; nothing need be known about the
	true dynamics away from the trajectory. A `Schedule` carries the measurement
	times, the per-coordinate (optional) box bounds observed at each, and the step
	count per segment. `Rec`, `segEnd`, `nodeAt` and `BuildTube` propagate an
	enclosing ball along the schedule, alternating "push across a segment" with
	"tighten using the next measurement".
- `DynaLean/DigitalTwin/MemBox.lean`: soundness of that construction.
	`ODE.tube_enclosure_global` says a successful run certifies a tube containing
	the real trajectory at every time of the horizon. `ODE.drift_sound` is the
	converse and the practically useful direction: if the construction fails, *no*
	trajectory satisfying the stated error budgets can have produced the observed
	measurements — the failure is a proof that the model has drifted.

The root module [`DynaLean.lean`](DynaLean.lean) imports only the basic and
definition modules. Every other module must be imported directly.

## Namespaces and notation

- Most results live in the `ODE` namespace.
- Euler scheme definitions and lemmas live in `Scheme` and `VectorScheme`.
- `ℝ^n` and `ℚ^n` (defined in `DynaLean/Defs.lean`) abbreviate
	`EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℚ (Fin n)`. A coercion
	`ℚ^n → ℝ^n` lets rational scheme data be compared with real solutions.
- Rational data is used wherever a quantity has to be computed rather than only
	reasoned about: exact arithmetic avoids any floating-point gap between what is
	evaluated and what is proved. Where a square root is unavoidable, `ODE.sqrtUB`
	rounds it outward, keeping every enclosure sound.

## Requirements

- Lean 4, using the version declared in [`lean-toolchain`](lean-toolchain)
- Lake, included with the Lean installation
- Git, so Lake can fetch Mathlib

The project currently follows the `mathlib` Git revision configured in
[`lakefile.toml`](lakefile.toml).

The library uses the Lean module system: every file begins with `module` and uses
`public import`.

## Getting Started

From the repository root, fetch dependencies and build the project:

```sh
lake update
lake build
```

The build compiles the `DynaLean` library and checks all Lean files in the
project. A successful build is the main verification command for this repo, and
is what CI runs (see [`.github/workflows`](.github/workflows)).

To work interactively, open the repository in VS Code with the Lean 4
extension installed. Lean will provide diagnostics and goal states while you
edit a `.lean` file. Every definition and theorem carries a doc comment, so
hovering over a name shows what it says and how it is proved.

## Example Imports

Import the root library:

```lean
import DynaLean
```

Or import a module containing a specific result:

```lean
import DynaLean.EulerBound
import DynaLean.Existence
```

## Tactics and commands

| name              | kind    | module                   | purpose                                                     |
| ----------------- | ------- | ------------------------ | ----------------------------------------------------------- |
| `#derive_bound`   | command | `DynaLean/Concrete.lean` | evaluate `S.x n` and emit a proved equality or bound         |
| `#make_proof`     | command | `DynaLean/MakeProof.lean`| generate a `HasBound` theorem and the enclosure it implies   |
| `apply_bound`     | tactic  | `DynaLean/MakeProof.lean`| close a `HasBound` goal by building the `n`-step derivation  |
| `apply_bound_vec` | tactic  | `DynaLean/MakeProof.lean`| the same for `HasBoundVec` in `ℚ^k`                          |

Each module ends with worked examples; `DynaLean/Concrete.lean` and
`DynaLean/MakeProof.lean` are the places to look first for usage.

## Project Status

DynaLean is an actively developed formalization. The APIs and theorem
statements may change as proofs and supporting definitions are refined.
