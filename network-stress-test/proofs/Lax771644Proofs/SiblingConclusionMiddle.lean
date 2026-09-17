import Lax771644Proofs.Ladder
import Lax771644.SiblingConclusionMiddle

/-!
Proofs for the concept `Lax771644.SiblingConclusionMiddle`.
-/

namespace Lax771644Proofs.SiblingConclusionMiddle

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.SiblingConclusionMiddle.s1
---
Statement 1 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s1 : Descent 32 31 :=
  descent 32 31 (by omega)

/--
---
conclusion: Lax771644.SiblingConclusionMiddle.s2
assumptions:
  - Lax771644.SiblingConclusionMiddle.s1
  - Lax771644.SiblingConclusionMiddle.s3
---
Statement 2 is the composite of the statements on either side of it.

# Proof strategy

Apply statement 1, then statement 3.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2 : Descent 32 30 := by
  intro n hn
  have h0 : Stage 32 n := hn
  have h1 : Stage 31 n := Lax771644.SiblingConclusionMiddle.s1 n (weaken 32 32 (by omega) h0)
  have h2 : Stage 30 n := Lax771644.SiblingConclusionMiddle.s3 n (weaken 31 31 (by omega) h1)
  exact weaken 30 30 (by omega) h2

/--
---
conclusion: Lax771644.SiblingConclusionMiddle.s3
---
Statement 3 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s3 : Descent 31 30 :=
  descent 31 30 (by omega)

end Lax771644Proofs.SiblingConclusionMiddle
