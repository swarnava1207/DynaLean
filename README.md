# DynaLean

DynaLean is a Lean 4 formalization of elementary results for ordinary
differential equations and numerical Euler schemes. It builds on
[Mathlib](https://github.com/leanprover-community/mathlib4) for analysis,
integration, derivatives, and inequalities.

## Contents

- `DynaLean/Defs.lean`: predicates for ODE solutions, interval clamping, and
	constant extensions of vector fields.
- `DynaLean/Existence.lean`: restriction and gluing of solutions, stepwise
	existence, Picard-Lindelof-based existence by induction, and existence for a
	vector field defined on a compact box.
- `DynaLean/Bounds.lean`: constant and time-dependent upper bounds for ODE
	solutions.
- `DynaLean/Comparison.lean`: first-order comparison of two ODE solutions.
- `DynaLean/Concrete.lean` : concrete examples of ODEs and Euler schemes, with a
    derivation of bounds for each.
- `DynaLean/Bihari.lean`: a Bihari-type integral bound for nonnegative
	solutions.
- `DynaLean/EulerScheme.lean`: rational Euler grids, iterates, and the
	piecewise-linear interpolant.
- `DynaLean/EulerBound.lean`: Taylor estimates and global error bounds for the
	Euler scheme, including a specialization whose final grid point is `T`.
- `DynaLean/Basic.lean`: minimal introductory declarations.

The root module [`DynaLean.lean`](DynaLean.lean) currently imports the basic
and definition modules. Individual modules can be imported directly when
using the additional results.

## Requirements

- Lean 4, using the version declared in [`lean-toolchain`](lean-toolchain)
- Lake, included with the Lean installation
- Git, so Lake can fetch Mathlib

The project currently follows the `mathlib` Git revision configured in
[`lakefile.toml`](lakefile.toml).

## Getting Started

From the repository root, fetch dependencies and build the project:

```sh
lake update
lake build
```

The build compiles the `DynaLean` library and checks all Lean files in the
project. A successful build is the main verification command for this repo.

To work interactively, open the repository in VS Code with the Lean 4
extension installed. Lean will provide diagnostics and goal states while you
edit a `.lean` file.

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

Most ODE results live in the `ODE` namespace. Euler scheme definitions and
lemmas live in the `Scheme` namespace.

## Project Status

DynaLean is an actively developed formalization. The APIs and theorem
statements may change as proofs and supporting definitions are refined.
