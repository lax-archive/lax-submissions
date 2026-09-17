import Lax771644Proofs.Ladder
import Lax771644.UnicodeNames

/-!
Proofs for the concept `Lax771644.UnicodeNames`.
-/

namespace Lax771644Proofs.UnicodeNames

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.UnicodeNames.μ_descent
---
The $\mu$ statement holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem mu : Descent 610 609 :=
  descent 610 609 (by omega)

/--
---
conclusion: Lax771644.UnicodeNames.εδ_descent
assumptions:
  - Lax771644.UnicodeNames.μ_descent
---
The $\varepsilon$–$\delta$ statement follows from the $\mu$ statement.

# Proof strategy

Apply the other statement and weaken one rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem epsilonDelta : Descent 610 608 := by
  intro n hn
  have h0 : Stage 610 n := hn
  have h1 : Stage 609 n := Lax771644.UnicodeNames.μ_descent n (weaken 610 610 (by omega) h0)
  exact weaken 609 608 (by omega) h1

end Lax771644Proofs.UnicodeNames
