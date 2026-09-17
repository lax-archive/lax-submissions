import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Cycle, first half
type: theorem
---
Half of a genuine cross-concept cycle: this statement is proved from the
statement of `CycleBeta`, which is in turn proved from this one. Neither becomes
proven — the archive's notion of provenness is a least fixed point — so both
should be drawn open and inside the grey display-cycle envelope.

# Formalization notes

The two statements are given the same type, which is the only way two proofs
can genuinely stand in for one another; each proof really is the other statement
and nothing else.
-/

namespace Lax771644.CycleAlpha

/-- Descent from stage 300 to stage 290. -/
axiom alpha : Foundations.Descent 300 290

end Lax771644.CycleAlpha
