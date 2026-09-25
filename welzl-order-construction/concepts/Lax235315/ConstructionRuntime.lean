import Lax235315.ConstructionContracts

/-!
---
title: Worst-case running time of the construction program
type: theorem
---
For all sufficiently large resource constants K, every run of the fixed
construction program on an admissible graph input halts within
K(|x|+1)(ceil(log₂ n)+1) steps, including unsuccessful random tapes.

# Formalization notes

This is an open implementation obligation for the explicit program.
It includes input reading, finite-bit sampling, the guarded arithmetic,
partition refinement, near-twin checking and reconstruction. Source-level
cost estimates alone do not discharge the registered word-RAM step bound.
-/

namespace Lax235315.ConstructionRuntime
open Lax235315.ConstructionContracts

/-- A constant suffices for the time bound on every admissible run. -/
axiom eventually_hasRunningTimeBound :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → HasRunningTimeBound K

end Lax235315.ConstructionRuntime
