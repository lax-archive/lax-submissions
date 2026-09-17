import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Sibling proof with the conclusion on the right
type: theorem
---
Three numbered statements, where statement 3 is proved from statements 1 and 2
of the same concept. This is the plain sibling-proof shape: the turnstile sits
below the rightmost dock and both of its assumption arrows come from docks to
its left.

# Formalization notes

The three rungs are chosen so that the composite really is the composite:
$12 \to 11$ followed by $11 \to 10$ gives $12 \to 10$.
-/

namespace Lax771644.SiblingConclusionRight

/-- Descent from stage 12 to stage 11. -/
axiom s1 : Foundations.Descent 12 11

/-- Descent from stage 11 to stage 10. -/
axiom s2 : Foundations.Descent 11 10

/-- Descent from stage 12 to stage 10, the composite of the two rungs above. -/
axiom s3 : Foundations.Descent 12 10

end Lax771644.SiblingConclusionRight
