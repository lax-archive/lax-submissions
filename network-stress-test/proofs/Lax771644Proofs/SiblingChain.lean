import Lax771644Proofs.Ladder
import Lax771644.SiblingChain

/-!
Proofs for the concept `Lax771644.SiblingChain`.
-/

namespace Lax771644Proofs.SiblingChain

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.SiblingChain.s1
---
Statement 1 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s1 : Descent 52 51 :=
  descent 52 51 (by omega)

/--
---
conclusion: Lax771644.SiblingChain.s2
assumptions:
  - Lax771644.SiblingChain.s1
---
Statement 2 follows from statement 1.

# Proof strategy

Apply statement 1, then weaken one further rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2 : Descent 52 50 := by
  intro n hn
  have h0 : Stage 52 n := hn
  have h1 : Stage 51 n := Lax771644.SiblingChain.s1 n (weaken 52 52 (by omega) h0)
  exact weaken 51 50 (by omega) h1

/--
---
conclusion: Lax771644.SiblingChain.s3
assumptions:
  - Lax771644.SiblingChain.s2
---
Statement 3 follows from statement 2.

# Proof strategy

Apply statement 2, then weaken one further rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s3 : Descent 52 49 := by
  intro n hn
  have h0 : Stage 52 n := hn
  have h1 : Stage 50 n := Lax771644.SiblingChain.s2 n (weaken 52 52 (by omega) h0)
  exact weaken 50 49 (by omega) h1

end Lax771644Proofs.SiblingChain
