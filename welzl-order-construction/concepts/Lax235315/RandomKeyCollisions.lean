import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
---
title: Collision bound for finite random keys
type: lemma
---
Give each of a vertices an independent uniform key from M possibilities.
The number of assignments with any repeated key is at most a² M^(a-1).
For M>0, division by M^a gives the probability bound a²/M.

# Formalization notes

Assignments are functions from Fin a to Fin M. Noninjectivity is exactly
the collision event, so no sampling implementation is built into the
statement. The counting form covers empty vertex or key sets as well;
the stated probability interpretation only uses M>0.
-/

namespace Lax235315.RandomKeyCollisions

/-- A union bound over distinct coordinate pairs bounds colliding key assignments. -/
axiom count_noninjective_le (a M : ℕ) :
    {f : Fin a → Fin M | ¬ Function.Injective f}.ncard ≤
      a ^ 2 * M ^ (a - 1)

end Lax235315.RandomKeyCollisions
