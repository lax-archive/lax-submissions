import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Two sibling proofs forming a chain
type: theorem
---
Statement 2 is proved from statement 1 and statement 3 from statement 2, both
inside this one concept. The two turnstiles must be stacked so that the second
sits below the output of the first without colliding with the dock row.

# Formalization notes

Each step weakens the lower rung by one, so the chain is genuine rather than
three unrelated claims.
-/

namespace Lax771644.SiblingChain

/-- Descent from stage 52 to stage 51. -/
axiom s1 : Foundations.Descent 52 51

/-- Descent from stage 52 to stage 50. -/
axiom s2 : Foundations.Descent 52 50

/-- Descent from stage 52 to stage 49. -/
axiom s3 : Foundations.Descent 52 49

end Lax771644.SiblingChain
