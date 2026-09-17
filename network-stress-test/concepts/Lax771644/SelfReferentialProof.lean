import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: A statement proved from itself
type: theorem
---
A one-element cycle: the only proof of this statement assumes the statement
itself. It stays unproven, and the drawing has to cope with a turnstile whose
assumption and conclusion are the same node.

# Formalization notes

Nothing subtle happens on the Lean side: an axiom may be used to prove a
theorem of its own type, and the archive then records the statement in its own
assumption set.
-/

namespace Lax771644.SelfReferentialProof

/-- Descent from stage 310 to stage 300. -/
axiom selfRung : Foundations.Descent 310 300

end Lax771644.SelfReferentialProof
