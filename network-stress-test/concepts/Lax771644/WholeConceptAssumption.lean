import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: A statement whose name is its concept's name
type: theorem
---
This concept declares one statement named exactly like the concept module
itself, alongside an ordinary numbered sibling. It is the closest the format
comes to a *whole-concept* assumption: a proof assuming it names the concept id
rather than a name below it.

# Formalization notes

Lean is happy to have a constant `Lax771644.WholeConceptAssumption` and a
constant `Lax771644.WholeConceptAssumption.s2` at the same time, exactly as it
has `Nat` and `Nat.succ`. The archive treats the first as an ordinary statement
of the module it originates in, so its identifier collides with the concept's
own identifier — which is the edge case this module exists to pin down.
-/

namespace Lax771644

/-- Descent from stage 320 to stage 319, declared with the concept's own name. -/
axiom WholeConceptAssumption : Foundations.Descent 320 319

end Lax771644

namespace Lax771644.WholeConceptAssumption

/-- Descent from stage 320 to stage 318. -/
axiom s2 : Foundations.Descent 320 318

end Lax771644.WholeConceptAssumption
