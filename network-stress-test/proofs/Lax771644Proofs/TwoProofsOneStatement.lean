import Lax771644Proofs.Ladder
import Lax771644.TwoProofsOneStatement

/-!
Proofs for the concept `Lax771644.TwoProofsOneStatement`.
-/

namespace Lax771644Proofs.TwoProofsOneStatement

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.TwoProofsOneStatement.s1
---
Statement 1 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s1 : Descent 62 61 :=
  descent 62 61 (by omega)

/--
---
conclusion: Lax771644.TwoProofsOneStatement.s2
---
Statement 2 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s2 : Descent 62 60 :=
  descent 62 60 (by omega)

/--
---
conclusion: Lax771644.TwoProofsOneStatement.s3
assumptions:
  - Lax771644.TwoProofsOneStatement.s1
---
First proof of statement 3, routed through statement 1.

# Proof strategy

Descend to stage 61 and weaken.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s3_via_s1 : Descent 62 55 := by
  intro n hn
  have h0 : Stage 62 n := hn
  have h1 : Stage 61 n := Lax771644.TwoProofsOneStatement.s1 n (weaken 62 62 (by omega) h0)
  exact weaken 61 55 (by omega) h1

/--
---
conclusion: Lax771644.TwoProofsOneStatement.s3
assumptions:
  - Lax771644.TwoProofsOneStatement.s2
---
Second proof of statement 3, routed through statement 2.

# Proof strategy

Descend to stage 60 and weaken.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s3_via_s2 : Descent 62 55 := by
  intro n hn
  have h0 : Stage 62 n := hn
  have h1 : Stage 60 n := Lax771644.TwoProofsOneStatement.s2 n (weaken 62 62 (by omega) h0)
  exact weaken 60 55 (by omega) h1

end Lax771644Proofs.TwoProofsOneStatement
