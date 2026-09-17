import Lax771644Proofs.Ladder
import Lax771644.SiblingChain
import Lax771644.SiblingConclusionMiddle
import Lax771644.ThreeProofsOneStatement

/-!
Proofs for the concept `Lax771644.ThreeProofsOneStatement`.
-/

namespace Lax771644Proofs.ThreeProofsOneStatement

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.ThreeProofsOneStatement.s1
---
Statement 1 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s1 : Descent 72 71 :=
  descent 72 71 (by omega)

/--
---
conclusion: Lax771644.ThreeProofsOneStatement.s2
assumptions:
  - Lax771644.ThreeProofsOneStatement.s1
---
First proof of statement 2: the sibling route.

# Proof strategy

Descend with statement 1 and weaken to stage 5.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2_via_sibling : Descent 72 5 := by
  intro n hn
  have h0 : Stage 72 n := hn
  have h1 : Stage 71 n := Lax771644.ThreeProofsOneStatement.s1 n (weaken 72 72 (by omega) h0)
  exact weaken 71 5 (by omega) h1

/--
---
conclusion: Lax771644.ThreeProofsOneStatement.s2
assumptions:
  - Lax771644.SiblingChain.s3
---
Second proof of statement 2, through a statement of `SiblingChain`.

# Proof strategy

Weaken to stage 52, descend with the foreign statement, weaken to stage 5.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2_via_sibling_chain : Descent 72 5 := by
  intro n hn
  have h0 : Stage 72 n := hn
  have h1 : Stage 49 n := Lax771644.SiblingChain.s3 n (weaken 72 52 (by omega) h0)
  exact weaken 49 5 (by omega) h1

/--
---
conclusion: Lax771644.ThreeProofsOneStatement.s2
assumptions:
  - Lax771644.SiblingConclusionMiddle.s2
---
Third proof of statement 2, through a statement of `SiblingConclusionMiddle`.

# Proof strategy

Weaken to stage 32, descend with the foreign statement, weaken to stage 5.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2_via_middle : Descent 72 5 := by
  intro n hn
  have h0 : Stage 72 n := hn
  have h1 : Stage 30 n := Lax771644.SiblingConclusionMiddle.s2 n (weaken 72 32 (by omega) h0)
  exact weaken 30 5 (by omega) h1

end Lax771644Proofs.ThreeProofsOneStatement
