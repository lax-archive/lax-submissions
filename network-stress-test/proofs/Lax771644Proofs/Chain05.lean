import Lax771644Proofs.Ladder
import Lax771644.Chain04
import Lax771644.Chain05

/-!
Proofs for the concept `Lax771644.Chain05`.
-/

namespace Lax771644Proofs.Chain05

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.Chain05.rung
assumptions:
  - Lax771644.Chain04.rung
---
Link 5 follows from link 4.

# Proof strategy

Apply the previous link and weaken one rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem rung : Descent 510 505 := by
  intro n hn
  have h0 : Stage 510 n := hn
  have h1 : Stage 506 n := Lax771644.Chain04.rung n (weaken 510 510 (by omega) h0)
  exact weaken 506 505 (by omega) h1

end Lax771644Proofs.Chain05
