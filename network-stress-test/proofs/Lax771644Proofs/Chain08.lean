import Lax771644Proofs.Ladder
import Lax771644.Chain07
import Lax771644.Chain08

/-!
Proofs for the concept `Lax771644.Chain08`.
-/

namespace Lax771644Proofs.Chain08

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.Chain08.rung
assumptions:
  - Lax771644.Chain07.rung
---
Link 8 follows from link 7.

# Proof strategy

Apply the previous link and weaken one rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem rung : Descent 510 502 := by
  intro n hn
  have h0 : Stage 510 n := hn
  have h1 : Stage 503 n := Lax771644.Chain07.rung n (weaken 510 510 (by omega) h0)
  exact weaken 503 502 (by omega) h1

end Lax771644Proofs.Chain08
