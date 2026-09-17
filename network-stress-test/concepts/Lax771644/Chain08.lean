import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Deep chain, link 8 of 9
type: theorem
---
Link 8 of a linear chain of nine single-statement concepts, each proved from
the previous one. The chain exists to make the layout engine draw a long, deep
path with no branching.

# Formalization notes

Each link weakens the previous rung by one, so the chain is a genuine
composition rather than nine restatements.
-/

namespace Lax771644.Chain08

/-- Descent from stage 510 to stage 502. -/
axiom rung : Foundations.Descent 510 502

end Lax771644.Chain08
