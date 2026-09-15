import Lax683916.SimpleGraphMultigraphRepresentation

namespace Lax683916Proofs.SimpleGraphMultigraphRepresentation

open Lax683916.MultigraphIsomorphism

universe u

private theorem ofSimpleGraph_simple {V : Type u} (H : SimpleGraph V) :
    (Graph.ofSimpleGraph H).Simple where
  not_isLoopAt e x h := by
    rw [Graph.IsLoopAt] at h
    obtain ⟨rfl, hxx⟩ := h
    exact H.loopless.irrefl x ((SimpleGraph.mem_edgeSet H).1 hxx)
  eq_of_isLink := by
    intro e f x y he hf
    exact he.1.trans hf.1.symm

/--
---
conclusion: Lax683916.SimpleGraphMultigraphRepresentation.exists_multigraph_representation
---
The canonical multigraph has all vertices, uses unordered vertex pairs as its
edge type, and retains exactly the edges of the simple graph.

# Proof strategy

Use mathlib's `Graph.ofSimpleGraph`. Its looplessness follows from the simple
graph's irreflexivity, and its endpoint equation makes parallel edges
impossible. The full vertex set is equivalent to the original vertex type,
the edge equivalence is the identity, and incidence preservation unfolds to
the defining endpoint equation.

# Attribution

Directly from `Mathlib.Combinatorics.Graph.Simple`.
-/
theorem exists_multigraph_representation {V : Type u} (H : SimpleGraph V) :
    ∃ G : Graph V (Sym2 V), G.Simple ∧ Nonempty (IsomorphicToSimpleGraph G H) := by
  let G := Graph.ofSimpleGraph H
  refine ⟨G, ofSimpleGraph_simple H, ⟨{
    vertexEquiv := Equiv.Set.univ V
    edgeEquiv := Equiv.refl H.edgeSet
    map_isLink := ?_ }⟩⟩
  intro e x y
  change (e.1 = s(x.1, y.1) ∧ e.1 ∈ H.edgeSet) ↔ e.1 = s(x.1, y.1)
  exact and_iff_left e.property

end Lax683916Proofs.SimpleGraphMultigraphRepresentation
