import Lax771644Proofs.Ladder
import Lax771644.Chain03
import Lax771644.Chain04

/-!
Proofs for the concept `Lax771644.Chain04`.
-/

namespace Lax771644Proofs.Chain04

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.Chain04.rung
assumptions:
  - Lax771644.Chain03.rung
---
Link 4 follows from link 3.

# Proof strategy

Apply the previous link and weaken one rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem rung : Descent 510 506 := by
  intro n hn
  have h0 : Stage 510 n := hn
  have h1 : Stage 507 n := Lax771644.Chain03.rung n (weaken 510 510 (by omega) h0)
  exact weaken 507 506 (by omega) h1

end Lax771644Proofs.Chain04
