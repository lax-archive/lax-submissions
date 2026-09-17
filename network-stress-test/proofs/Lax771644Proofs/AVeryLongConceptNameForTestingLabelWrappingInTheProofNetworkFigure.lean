import Lax771644Proofs.Ladder
import Lax771644.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure

/-!
Proofs for the concept `Lax771644.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure`.
-/

namespace Lax771644Proofs.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure.everyDescentAlongTheBenchmarkLadderSurvivesWeakeningOfItsUpperRung
---
The first overlong statement holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem first : Descent 600 599 :=
  descent 600 599 (by omega)

/--
---
conclusion: Lax771644.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure.theSecondDeliberatelyOverlongStatementNameInThisConceptModule
assumptions:
  - Lax771644.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure.everyDescentAlongTheBenchmarkLadderSurvivesWeakeningOfItsUpperRung
---
The second overlong statement follows from the first.

# Proof strategy

Apply the first statement and weaken one rung.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem second : Descent 600 598 := by
  intro n hn
  have h0 : Stage 600 n := hn
  have h1 : Stage 599 n := Lax771644.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure.everyDescentAlongTheBenchmarkLadderSurvivesWeakeningOfItsUpperRung n (weaken 600 600 (by omega) h0)
  exact weaken 599 598 (by omega) h1

end Lax771644Proofs.AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure
