import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Sibling proof with the conclusion in the middle
type: theorem
---
Statement 2 is proved from statements 1 and 3, so the turnstile sits below the
middle dock with one assumption arriving from the left and one from the right.

# Formalization notes

Again the same ladder in a fresh band of rungs.
-/

namespace Lax771644.SiblingConclusionMiddle

/-- Descent from stage 32 to stage 31. -/
axiom s1 : Foundations.Descent 32 31

/-- Descent from stage 32 to stage 30, the composite of its two neighbours. -/
axiom s2 : Foundations.Descent 32 30

/-- Descent from stage 31 to stage 30. -/
axiom s3 : Foundations.Descent 31 30

end Lax771644.SiblingConclusionMiddle
