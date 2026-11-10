module

public import DynaLean.Basic
public import DynaLean.Defs

/-! # DynaLean

Root module of the DynaLean library: a Lean 4 formalization of elementary results for
ordinary differential equations and their numerical (Euler) approximations.

Importing `DynaLean` pulls in only the two foundational modules:

* `DynaLean.Basic` — a minimal sanity-check declaration;
* `DynaLean.Defs`  — the `ODE.SolutionExists` / `ODE.SolutionExistsVector` predicates,
  the `ℝ^n` / `ℚ^n` notation, interval clamping and the constant extension of a
  locally defined vector field.

Every other result lives in a module that must be imported explicitly, e.g.

```lean
import DynaLean.Existence   -- existence and uniqueness of solutions
import DynaLean.EulerBound  -- global error bounds for the Euler scheme
```

Analytic results live in the `ODE` namespace; Euler scheme definitions live in the
`Scheme` / `VectorScheme` namespaces.
-/
