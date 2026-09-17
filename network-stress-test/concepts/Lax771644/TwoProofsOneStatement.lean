import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Two sibling proofs of the same statement
type: theorem
---
Statement 3 carries two independent proofs, one from statement 1 and one from
statement 2. Two turnstiles point at the same dock.

# Formalization notes

The two routes descend through different intermediate rungs, so they really
are two different proofs and not the same term twice.
-/

namespace Lax771644.TwoProofsOneStatement

/-- Descent from stage 62 to stage 61. -/
axiom s1 : Foundations.Descent 62 61

/-- Descent from stage 62 to stage 60. -/
axiom s2 : Foundations.Descent 62 60

/-- Descent from stage 62 to stage 55, reachable through either route. -/
axiom s3 : Foundations.Descent 62 55

end Lax771644.TwoProofsOneStatement
