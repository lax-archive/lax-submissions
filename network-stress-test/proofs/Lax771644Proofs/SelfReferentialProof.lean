import Lax771644Proofs.Ladder
import Lax771644.SelfReferentialProof

/-!
Proofs for the concept `Lax771644.SelfReferentialProof`.
-/

namespace Lax771644Proofs.SelfReferentialProof

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.SelfReferentialProof.selfRung
assumptions:
  - Lax771644.SelfReferentialProof.selfRung
---
The statement, proved from itself.

# Proof strategy

Apply the statement to its own goal. Circular by design; the archive's least fixed point leaves it unproven.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem selfRung : Descent 310 300 := by
  intro n hn
  have h0 : Stage 310 n := hn
  have h1 : Stage 300 n := Lax771644.SelfReferentialProof.selfRung n (weaken 310 310 (by omega) h0)
  exact weaken 300 300 (by omega) h1

end Lax771644Proofs.SelfReferentialProof
