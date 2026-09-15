import Lax683916.MultigraphIsomorphism

/-!
---
title: Multigraph representation of a simple graph
type: theorem
---
Every simple graph has a simple loopless multigraph representation with the
same vertices. The actual edges of the multigraph correspond bijectively to
the unordered edges of the simple graph, and the correspondence preserves
endpoints.

# Formalization notes

The statement gives one multigraph witness together with its simplicity and
the vertex-and-edge isomorphism. Its edge type is the canonical type `Sym2 V`
of all unordered vertex pairs; only graph edges belong to its actual edge
set. This is the converse of the multigraph-to-simple-graph representation
theorem.
-/

namespace Lax683916.SimpleGraphMultigraphRepresentation

open Lax683916.MultigraphIsomorphism

universe u

/-- Every simple graph is represented by a simple multigraph on its vertices. -/
axiom exists_multigraph_representation {V : Type u} (H : SimpleGraph V) :
  ∃ G : Graph V (Sym2 V), G.Simple ∧ Nonempty (IsomorphicToSimpleGraph G H)

end Lax683916.SimpleGraphMultigraphRepresentation
