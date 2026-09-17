import Lax771644Proofs.Ladder
import Lax771644.SiblingConclusionLeft

/-!
Proofs for the concept `Lax771644.SiblingConclusionLeft`.
-/

namespace Lax771644Proofs.SiblingConclusionLeft

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.SiblingConclusionLeft.s1
assumptions:
  - Lax771644.SiblingConclusionLeft.s2
  - Lax771644.SiblingConclusionLeft.s3
---
Statement 1 is the composite of its two siblings to the right.

# Proof strategy

Apply statement 2, then statement 3.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s1 : Descent 22 20 := by
  intro n hn
  have h0 : Stage 22 n := hn
  have h1 : Stage 21 n := Lax771644.SiblingConclusionLeft.s2 n (weaken 22 22 (by omega) h0)
  have h2 : Stage 20 n := Lax771644.SiblingConclusionLeft.s3 n (weaken 21 21 (by omega) h1)
  exact weaken 20 20 (by omega) h2

/--
---
conclusion: Lax771644.SiblingConclusionLeft.s2
---
Statement 2 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2 : Descent 22 21 :=
  descent 22 21 (by omega)

/--
---
conclusion: Lax771644.SiblingConclusionLeft.s3
---
Statement 3 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s3 : Descent 21 20 :=
  descent 21 20 (by omega)

end Lax771644Proofs.SiblingConclusionLeft
