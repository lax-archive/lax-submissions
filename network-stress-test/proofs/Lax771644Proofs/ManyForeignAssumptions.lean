import Lax771644Proofs.Ladder
import Lax771644.ManyForeignAssumptions
import Lax771644.MixedSiblingAndForeign
import Lax771644.SiblingChain
import Lax771644.SiblingConclusionLeft
import Lax771644.SiblingConclusionMiddle
import Lax771644.SiblingConclusionRight
import Lax771644.ThreeProofsOneStatement
import Lax771644.TwoProofsOneStatement
import Lax771644.WideDockRow

/-!
Proofs for the concept `Lax771644.ManyForeignAssumptions`.
-/

namespace Lax771644Proofs.ManyForeignAssumptions

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.ManyForeignAssumptions.descends_far
assumptions:
  - Lax771644.MixedSiblingAndForeign.s1
  - Lax771644.SiblingChain.s3
  - Lax771644.SiblingConclusionLeft.s1
  - Lax771644.SiblingConclusionMiddle.s2
  - Lax771644.SiblingConclusionRight.s3
  - Lax771644.ThreeProofsOneStatement.s1
  - Lax771644.TwoProofsOneStatement.s3
  - Lax771644.WideDockRow.s12
---
The long descent, assembled from one statement of each of eight concepts.

# Proof strategy

Weaken into each assumed rung in turn and apply it.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem descends_far : Descent 200 10 := by
  intro n hn
  have h0 : Stage 200 n := hn
  have h1 : Stage 100 n := Lax771644.WideDockRow.s12 n (weaken 200 111 (by omega) h0)
  have h2 : Stage 71 n := Lax771644.ThreeProofsOneStatement.s1 n (weaken 100 72 (by omega) h1)
  have h3 : Stage 55 n := Lax771644.TwoProofsOneStatement.s3 n (weaken 71 62 (by omega) h2)
  have h4 : Stage 49 n := Lax771644.SiblingChain.s3 n (weaken 55 52 (by omega) h3)
  have h5 : Stage 40 n := Lax771644.MixedSiblingAndForeign.s1 n (weaken 49 42 (by omega) h4)
  have h6 : Stage 30 n := Lax771644.SiblingConclusionMiddle.s2 n (weaken 40 32 (by omega) h5)
  have h7 : Stage 20 n := Lax771644.SiblingConclusionLeft.s1 n (weaken 30 22 (by omega) h6)
  have h8 : Stage 10 n := Lax771644.SiblingConclusionRight.s3 n (weaken 20 12 (by omega) h7)
  exact weaken 10 10 (by omega) h8

end Lax771644Proofs.ManyForeignAssumptions
