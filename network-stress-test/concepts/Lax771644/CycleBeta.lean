import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Cycle, second half
type: theorem
---
The other half of the cycle with `CycleAlpha`. Its proof assumes
`CycleAlpha.alpha`, whose proof assumes this statement.

# Formalization notes

See `CycleAlpha` for why the two statements share a type.
-/

namespace Lax771644.CycleBeta

/-- Descent from stage 300 to stage 290. -/
axiom beta : Foundations.Descent 300 290

end Lax771644.CycleBeta
