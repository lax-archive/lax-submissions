import Lax771644Proofs.Ladder
import Lax771644.Chain01
import Lax771644.Chain02

/-!
Proofs for the concept `Lax771644.Chain02`.
-/

namespace Lax771644Proofs.Chain02

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.Chain02.rung
assumptions:
  - Lax771644.Chain01.rung
---
Link 2 follows from link 1.

# Proof strategy

Apply the previous link and weaken one rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem rung : Descent 510 508 := by
  intro n hn
  have h0 : Stage 510 n := hn
  have h1 : Stage 509 n := Lax771644.Chain01.rung n (weaken 510 510 (by omega) h0)
  exact weaken 509 508 (by omega) h1

end Lax771644Proofs.Chain02
