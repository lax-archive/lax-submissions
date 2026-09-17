import Lax771644Proofs.Ladder
import Lax771644.OpenMiddle
import Lax771644.OpenRoot

/-!
Proofs for the concept `Lax771644.OpenMiddle`.
-/

namespace Lax771644Proofs.OpenMiddle

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.OpenMiddle.middleRung
assumptions:
  - Lax771644.OpenRoot.openRung
---
Follows from the open root statement.

# Proof strategy

Apply the open statement and weaken one further rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem middleRung : Descent 400 380 := by
  intro n hn
  have h0 : Stage 400 n := hn
  have h1 : Stage 390 n := Lax771644.OpenRoot.openRung n (weaken 400 400 (by omega) h0)
  exact weaken 390 380 (by omega) h1

end Lax771644Proofs.OpenMiddle
