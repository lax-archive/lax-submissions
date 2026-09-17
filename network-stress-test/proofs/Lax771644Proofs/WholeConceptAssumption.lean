import Lax771644Proofs.Ladder
import Lax771644.WholeConceptAssumption

/-!
Proofs for the concept `Lax771644.WholeConceptAssumption`.
-/

namespace Lax771644Proofs.WholeConceptAssumption

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.WholeConceptAssumption
---
The concept-named statement holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem bare : Descent 320 319 :=
  descent 320 319 (by omega)

/--
---
conclusion: Lax771644.WholeConceptAssumption.s2
assumptions:
  - Lax771644.WholeConceptAssumption
---
The numbered sibling follows from the concept-named statement.

# Proof strategy

Apply the concept-named statement and weaken one rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2 : Descent 320 318 := by
  intro n hn
  have h0 : Stage 320 n := hn
  have h1 : Stage 319 n := Lax771644.WholeConceptAssumption n (weaken 320 320 (by omega) h0)
  exact weaken 319 318 (by omega) h1

end Lax771644Proofs.WholeConceptAssumption
