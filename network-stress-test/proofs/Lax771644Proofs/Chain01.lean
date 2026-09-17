import Lax771644Proofs.Ladder
import Lax771644.Chain01

/-!
Proofs for the concept `Lax771644.Chain01`.
-/

namespace Lax771644Proofs.Chain01

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.Chain01.rung
---
The first link holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem rung : Descent 510 509 :=
  descent 510 509 (by omega)

end Lax771644Proofs.Chain01
