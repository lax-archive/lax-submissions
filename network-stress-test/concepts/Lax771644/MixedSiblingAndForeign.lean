import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Mixed proof: one sibling and one foreign assumption
type: theorem
---
Statement 2 is proved from statement 1 of this concept *and* from statement 3
of `SiblingConclusionRight`. One assumption arrow is local, the other crosses to
another concept box, so the drawing has to place a turnstile that is a sibling
proof on one side and a cross-concept proof on the other.

# Formalization notes

The foreign rung $12 \to 10$ picks up exactly where the local rung
$42 \to 40$ leaves off, after a free weakening from stage 40 to stage 12.
-/

namespace Lax771644.MixedSiblingAndForeign

/-- Descent from stage 42 to stage 40. -/
axiom s1 : Foundations.Descent 42 40

/-- Descent from stage 42 all the way down to stage 10. -/
axiom s2 : Foundations.Descent 42 10

end Lax771644.MixedSiblingAndForeign
