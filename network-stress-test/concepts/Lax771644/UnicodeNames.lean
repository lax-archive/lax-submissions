import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: Ünïcode: $\mu$-descent and $\varepsilon$–$\delta$ weakening (ℵ₀ rungs, ∀∃, 中文)
type: theorem
---
A concept whose title and whose statement names carry non-ASCII characters, to
check that the figure's labels, tooltips and anchors survive them. The Greek
letters have no mathematical meaning here.

# Formalization notes

`εδ_descent` sorts before `μ_descent` by code point, so the concept-named
docks come out in the order ε, μ and the sibling proof again has its conclusion
on the left.
-/

namespace Lax771644.UnicodeNames

/-- Descent from stage 610 to stage 608. -/
axiom εδ_descent : Foundations.Descent 610 608

/-- Descent from stage 610 to stage 609. -/
axiom μ_descent : Foundations.Descent 610 609

end Lax771644.UnicodeNames
