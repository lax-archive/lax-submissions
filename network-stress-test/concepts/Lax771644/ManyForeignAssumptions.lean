import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: One proof assuming eight other concepts
type: theorem
---
A single-statement concept whose proof assumes one statement from each of eight
different concepts of this submission. Every one of those uses is coarsened by
the drawing to a single port on the assumed concept's box, so this is the test
for a wide rail of *cross-concept* assumption arrows.

# Formalization notes

The eight foreign rungs are chosen to descend, so the composite from stage 200
down to stage 10 uses each of them.
-/

namespace Lax771644.ManyForeignAssumptions

/-- Descent from stage 200 to stage 10, assembled from eight other concepts. -/
axiom descends_far : Foundations.Descent 200 10

end Lax771644.ManyForeignAssumptions
