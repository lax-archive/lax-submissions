import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: An open statement nothing proves
type: theorem
---
A single-statement concept with no proof at all. Everything downstream of it
stays unproven, which is what the next two concepts are for.

# Formalization notes

No proof module mentions this statement as a conclusion.
-/

namespace Lax771644.OpenRoot

/-- Descent from stage 400 to stage 390. Deliberately left unproven. -/
axiom openRung : Foundations.Descent 400 390

end Lax771644.OpenRoot
