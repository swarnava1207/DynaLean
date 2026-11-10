module

/-! # Basic

A deliberately minimal module. It carries no mathematics; it exists so that the root
module `DynaLean` always has something to import, and so that `lake build` fails fast
and informatively if the toolchain or the Mathlib dependency is misconfigured.
-/

/-- A minimal declaration used to verify that the project imports correctly. -/
def hello := "world"
