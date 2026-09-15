import Mathlib.Data.Set.Card

/-!
---
title: 2-uniform set system
type: definition
---
A 2-uniform set system on a ground type `V` is a family of subsets of `V`,
each containing exactly two elements.

# Formalization notes

The family is represented as `Set (Set V)`, so it has neither repeated
members nor a separate ambient vertex set. No looplessness field is carried:
a singleton has cardinality one, so 2-uniformity already excludes loops.
-/

namespace Lax683916.TwoUniformSetSystems

/-- A family of two-element subsets of `V`. -/
structure TwoUniformSetSystem (V : Type*) where
  /-- The sets belonging to the family. -/
  sets : Set (Set V)
  /-- Every member of the family has exactly two elements. -/
  twoUniform : ∀ s ∈ sets, Set.ncard s = 2

end Lax683916.TwoUniformSetSystems
