import Lax771644Proofs.Ladder
import Lax771644.MixedSiblingAndForeign
import Lax771644.SiblingConclusionRight

/-!
Proofs for the concept `Lax771644.MixedSiblingAndForeign`.
-/

namespace Lax771644Proofs.MixedSiblingAndForeign

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.MixedSiblingAndForeign.s1
---
Statement 1 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s1 : Descent 42 40 :=
  descent 42 40 (by omega)

/--
---
conclusion: Lax771644.MixedSiblingAndForeign.s2
assumptions:
  - Lax771644.MixedSiblingAndForeign.s1
  - Lax771644.SiblingConclusionRight.s3
---
Statement 2 chains a sibling statement into a statement of another concept.

# Proof strategy

Descend with the sibling statement to stage 40, weaken to stage 12, and finish with the foreign statement.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2 : Descent 42 10 := by
  intro n hn
  have h0 : Stage 42 n := hn
  have h1 : Stage 40 n := Lax771644.MixedSiblingAndForeign.s1 n (weaken 42 42 (by omega) h0)
  have h2 : Stage 10 n := Lax771644.SiblingConclusionRight.s3 n (weaken 40 12 (by omega) h1)
  exact weaken 10 10 (by omega) h2

end Lax771644Proofs.MixedSiblingAndForeign
