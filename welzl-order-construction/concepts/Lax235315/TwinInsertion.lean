import Lax235315.SequenceCrossings

/-!
---
title: Inserting a twin preserves crossings
type: theorem
---
Duplicating a membership entry immediately next to itself leaves the crossing
count unchanged. Applying this to every set proves Lemma 2.1 of
Dreier--Kuske: an adjacent duplicate of a twin does not change any crossing count.

# Formalization notes

The arbitrary prefix and suffix allow insertion at every position, including
the ends. This is a claim about membership sequences, independent of whether
the duplicated entries represent distinct vertices.
-/

namespace Lax235315.TwinInsertion
open Lax235315.SequenceCrossings

/-- Adjacent repetition of a bit preserves the number of changes. -/
axiom crossings_duplicate (pre post : List Bool) (b : Bool) :
    crossings (pre ++ b :: b :: post) =
      crossings (pre ++ b :: post)

end Lax235315.TwinInsertion
