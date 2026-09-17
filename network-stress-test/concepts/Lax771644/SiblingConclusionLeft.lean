import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Sibling proof with the conclusion on the left
type: theorem
---
The mirror image of the previous concept: statement 1 is proved from statements
2 and 3. The turnstile therefore sits below the *leftmost* dock while both of
its assumption arrows arrive from docks to its right.

# Formalization notes

Same ladder, different band of rungs, so that the two concepts cannot be
confused when both are on screen.
-/

namespace Lax771644.SiblingConclusionLeft

/-- Descent from stage 22 to stage 20, the composite of the two rungs below. -/
axiom s1 : Foundations.Descent 22 20

/-- Descent from stage 22 to stage 21. -/
axiom s2 : Foundations.Descent 22 21

/-- Descent from stage 21 to stage 20. -/
axiom s3 : Foundations.Descent 21 20

end Lax771644.SiblingConclusionLeft
