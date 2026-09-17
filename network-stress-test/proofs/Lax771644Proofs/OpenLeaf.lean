import Lax771644Proofs.Ladder
import Lax771644.OpenLeaf
import Lax771644.OpenMiddle

/-!
Proofs for the concept `Lax771644.OpenLeaf`.
-/

namespace Lax771644Proofs.OpenLeaf

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.OpenLeaf.leafRung
assumptions:
  - Lax771644.OpenMiddle.middleRung
---
Follows from the middle of the open chain.

# Proof strategy

Apply the middle statement and weaken one further rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem leafRung : Descent 400 370 := by
  intro n hn
  have h0 : Stage 400 n := hn
  have h1 : Stage 380 n := Lax771644.OpenMiddle.middleRung n (weaken 400 400 (by omega) h0)
  exact weaken 380 370 (by omega) h1

end Lax771644Proofs.OpenLeaf
