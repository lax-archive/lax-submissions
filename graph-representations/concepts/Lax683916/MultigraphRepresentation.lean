import Lax683916.MultigraphIsomorphism

/-!
---
title: Simple-graph representation of a simple multigraph
type: theorem
---
Every simple loopless multigraph is a simple graph up to simultaneous
isomorphism of its actual vertex and edge sets. Incidence is preserved: an
edge has endpoints `u` and `v` precisely when its image is the unordered edge
joining the images of `u` and `v`.

# Formalization notes

The isomorphism notion is supplied by the companion definition concept.
Mathlib's `Graph.Simple` already includes looplessness and uniqueness of an
edge with given endpoints. The theorem chooses `G.vertexSet` as its canonical
simple-graph carrier; the isomorphism definition also permits subsequent
changes of vertex type.
-/

namespace Lax683916.MultigraphRepresentation

open Lax683916.MultigraphIsomorphism

universe u v

/-- Every simple multigraph is isomorphic to a simple graph on its actual vertex set. -/
axiom exists_simpleGraph_representation {α : Type u} {β : Type v}
    (G : Graph α β) [G.Simple] :
  ∃ H : SimpleGraph G.vertexSet, Nonempty (IsomorphicToSimpleGraph G H)

end Lax683916.MultigraphRepresentation
