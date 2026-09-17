import Lax771644Proofs.Ladder
import Lax771644.CycleAlpha
import Lax771644.CycleBeta

/-!
Proofs for the concept `Lax771644.CycleAlpha`.
-/

namespace Lax771644Proofs.CycleAlpha

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.CycleAlpha.alpha
assumptions:
  - Lax771644.CycleBeta.beta
---
This statement holds if the statement of `CycleBeta` does.

# Proof strategy

Apply `CycleBeta.beta` verbatim. Circular by design: the converse proof assumes this statement.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem alpha : Descent 300 290 := by
  intro n hn
  have h0 : Stage 300 n := hn
  have h1 : Stage 290 n := Lax771644.CycleBeta.beta n (weaken 300 300 (by omega) h0)
  exact weaken 290 290 (by omega) h1

end Lax771644Proofs.CycleAlpha
