import Lax235315.ConstructionContracts

/-!
---
title: Success probability of the construction program
type: theorem
---
For all sufficiently large resource constants K, at least two thirds of the
equally likely finite random tapes cause an admissible construction run to
reach the final halt with the success flag set.

# Formalization notes

This is an open probability obligation for the explicit program, not for an
ideal uniform-sampling oracle. Its proof must account for collisions of the
finite random keys, conditional sampling at every adaptive round, and the
available tape length. Output quality is proved separately.
-/

namespace Lax235315.ConstructionProbability
open Lax235315.ConstructionContracts

/-- At least two thirds of the finite tapes lead to successful termination. -/
axiom eventually_hasSuccessProbability :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → HasSuccessProbability K

end Lax235315.ConstructionProbability
