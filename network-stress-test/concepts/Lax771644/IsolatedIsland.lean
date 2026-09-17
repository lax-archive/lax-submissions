import Mathlib.Data.Nat.Notation

/-!
---
title: Isolated island (no statements, no uses)
type: definition
---
A definition-concept that declares no statement, imports no other concept of
this submission, and is imported by none. It is here to check that the drawing
places a concept with no incident edge at all.

# Formalization notes

The marker predicate is never used anywhere. Its only purpose is to give
this module a declaration so that it is a concept rather than an empty file.
-/

namespace Lax771644.IsolatedIsland

/-- A marker predicate that nothing in this submission ever mentions. -/
def marker : Prop := ∀ n : ℕ, n = n

end Lax771644.IsolatedIsland
