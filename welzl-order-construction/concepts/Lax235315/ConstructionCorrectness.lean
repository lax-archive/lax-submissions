import Lax235315.ConstructionContracts

/-!
---
title: Correct outputs of the construction program
type: theorem
---
For all sufficiently large resource constants K, an admissible execution
that reaches the final halt with the success flag set outputs every graph
vertex exactly once, in an order crossed at most
12c² ceil(log₂ n)² times by every open neighborhood.

# Formalization notes

This is an open bridge from concrete machine execution to the deterministic
contraction and reconstruction argument. No probability conclusion is assumed
or asserted. Empty and singleton graphs are included in the contract.
-/

namespace Lax235315.ConstructionCorrectness
open Lax235315.ConstructionContracts

/-- Successful machine executions satisfy the exact registered output relation. -/
axiom eventually_hasCorrectOutput :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → HasCorrectOutput K

end Lax235315.ConstructionCorrectness
