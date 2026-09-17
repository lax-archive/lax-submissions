import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Middle of an open chain
type: theorem
---
Proved from `OpenRoot`, which is unproven, so this statement is unproven too
although it has a proof. The drawing should show a complete turnstile above an
open dock.

# Formalization notes

Proven *relative to* `OpenRoot.openRung`, in the spec's terminology.
-/

namespace Lax771644.OpenMiddle

/-- Descent from stage 400 to stage 380. -/
axiom middleRung : Foundations.Descent 400 380

end Lax771644.OpenMiddle
