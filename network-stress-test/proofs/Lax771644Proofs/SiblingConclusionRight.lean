import Lax771644Proofs.Ladder
import Lax771644.SiblingConclusionRight

/-!
Proofs for the concept `Lax771644.SiblingConclusionRight`.
-/

namespace Lax771644Proofs.SiblingConclusionRight

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.SiblingConclusionRight.s1
---
Statement 1 holds outright, by weakening the ladder.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s1 : Descent 12 11 :=
  descent 12 11 (by omega)

/--
---
conclusion: Lax771644.SiblingConclusionRight.s2
---
Statement 2 holds outright, by weakening the ladder.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2 : Descent 11 10 :=
  descent 11 10 (by omega)

/--
---
conclusion: Lax771644.SiblingConclusionRight.s3
assumptions:
  - Lax771644.SiblingConclusionRight.s1
  - Lax771644.SiblingConclusionRight.s2
---
Statement 3 is the composite of its two siblings.

# Proof strategy

Apply statement 1 to descend to stage 11, then statement 2 to descend to stage 10.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s3 : Descent 12 10 := by
  intro n hn
  have h0 : Stage 12 n := hn
  have h1 : Stage 11 n := Lax771644.SiblingConclusionRight.s1 n (weaken 12 12 (by omega) h0)
  have h2 : Stage 10 n := Lax771644.SiblingConclusionRight.s2 n (weaken 11 11 (by omega) h1)
  exact weaken 10 10 (by omega) h2

end Lax771644Proofs.SiblingConclusionRight
