import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax17.Degree
import Lax17.SpanningTreeRounding

/-!
---
title: Singh--Lau bounded-degree spanning-tree theorem
type: theorem
---
A feasible bounded-degree spanning-tree point can be rounded with an
additive-one loss in the maximum degree.
-/

namespace Lax17.SinghLau

universe u

/-- Singh--Lau additive-one bounded-degree spanning-tree rounding. -/
axiom singhLauBoundedDegreeSpanningTree :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : ℕ),
      1 < Fintype.card V →
        Lax17.SpanningTreeRounding.FeasiblePoint G B →
          ∃ T : SimpleGraph V,
            T ≤ G ∧ T.IsTree ∧ Lax17.Degree.MaximumAtMost T (B + 1)

end Lax17.SinghLau
