import Mathlib.Data.Rat.Defs
import Lax17.Degree

/-!
---
title: Bounded-degree spanning-tree relaxation
type: definition
---
A feasible bounded-degree spanning-tree point assigns nonnegative rational
weights to the edges, has total weight \(|V|-1\), satisfies every forest
inequality, and has fractional degree at most \(B\) at every vertex.  This is
the unweighted relaxation used by the Singh--Lau rounding theorem.
-/

namespace Lax17.SpanningTreeRounding

universe u

open Finset

/-- Both endpoints of an unordered pair lie in `S`. -/
def PairInside {V : Type u} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  e.toFinset ⊆ S

/-- The finite edge set of `G`. -/
noncomputable def edges {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeSet.toFinite.toFinset

/-- The edges of `G` with both endpoints in `S`. -/
noncomputable def internalEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  @Finset.filter (Sym2 V) (PairInside S) (Classical.decPred _) (edges G)

/-- The edges of `G` incident with `v`. -/
noncomputable def incidentEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset (Sym2 V) :=
  (edges G).filter fun e => v ∈ e

/-- A feasible point of the bounded-degree spanning-tree relaxation. -/
structure FeasiblePoint {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : ℕ) where
  weight : Sym2 V → ℚ
  nonnegative : ∀ e : Sym2 V, e ∈ edges G → 0 ≤ weight e
  total :
    (edges G).sum weight = (Fintype.card V - 1 : ℕ)
  forest :
    ∀ S : Finset V, S ≠ Finset.univ →
      (internalEdges G S).sum weight ≤ (S.card - 1 : ℕ)
  degree :
    ∀ v : V, (incidentEdges G v).sum weight ≤ B

end Lax17.SpanningTreeRounding
