import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: One statement with three proofs
type: theorem
---
Statement 2 is the conclusion of three different proofs: one sibling proof from
statement 1 of this concept, and two proofs whose assumptions live in other
concepts. Three turnstiles have to fan into a single dock.

# Formalization notes

Statement 2 descends far enough that any of the three routes reaches it.
-/

namespace Lax771644.ThreeProofsOneStatement

/-- Descent from stage 72 to stage 71. -/
axiom s1 : Foundations.Descent 72 71

/-- Descent from stage 72 down to stage 5. -/
axiom s2 : Foundations.Descent 72 5

end Lax771644.ThreeProofsOneStatement
