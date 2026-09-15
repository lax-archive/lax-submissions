import Mathlib.Combinatorics.Graph.Simple

/-!
---
title: Isomorphism from a multigraph to a simple graph
type: definition
---
A multigraph and a simple graph are isomorphic when their actual vertex and
edge sets are in bijection and these bijections preserve endpoints.

# Formalization notes

`Graph α β` stores vertex and edge sets inside ambient types, whereas
`SimpleGraph V` takes the vertex type itself as its vertex set and represents
edges canonically as unordered pairs. The comparison therefore uses
equivalences between the subtypes `G.vertexSet` and `G.edgeSet`, not between
the ambient types `α`, `β` and the canonical carriers.
-/

namespace Lax683916.MultigraphIsomorphism

/-- An incidence-preserving vertex-and-edge isomorphism from a multigraph to a simple graph. -/
structure IsomorphicToSimpleGraph {α β V : Type*} (G : Graph α β) (H : SimpleGraph V) where
  /-- The bijection between the actual vertices of the two graphs. -/
  vertexEquiv : G.vertexSet ≃ V
  /-- The bijection between the actual edges of the two graphs. -/
  edgeEquiv : G.edgeSet ≃ H.edgeSet
  /-- The vertex and edge bijections preserve the endpoint relation. -/
  map_isLink : ∀ (e : G.edgeSet) (u v : G.vertexSet),
    G.IsLink e.1 u.1 v.1 ↔
      (edgeEquiv e).1 = s(vertexEquiv u, vertexEquiv v)

end Lax683916.MultigraphIsomorphism
