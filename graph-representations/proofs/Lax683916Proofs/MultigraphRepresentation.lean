import Lax683916.MultigraphRepresentation

namespace Lax683916Proofs.MultigraphRepresentation

open Lax683916.MultigraphIsomorphism

universe u v

variable {α : Type u} {β : Type v} (G : Graph α β)

/-- A chosen left endpoint of an edge. -/
noncomputable def edgeLeft (e : G.edgeSet) : α :=
  Classical.choose (G.exists_isLink_of_mem_edgeSet e.property)

/-- A chosen right endpoint of an edge. -/
noncomputable def edgeRight (e : G.edgeSet) : α :=
  Classical.choose (Classical.choose_spec (G.exists_isLink_of_mem_edgeSet e.property))

/-- The chosen endpoints do form the original edge. -/
theorem edge_isLink (e : G.edgeSet) : G.IsLink e.1 (edgeLeft G e) (edgeRight G e) :=
  Classical.choose_spec (Classical.choose_spec (G.exists_isLink_of_mem_edgeSet e.property))

/-- The chosen left endpoint, regarded as an actual vertex of the graph. -/
noncomputable def edgeLeftVertex (e : G.edgeSet) : G.vertexSet :=
  ⟨edgeLeft G e, (edge_isLink G e).left_mem⟩

/-- The chosen right endpoint, regarded as an actual vertex of the graph. -/
noncomputable def edgeRightVertex (e : G.edgeSet) : G.vertexSet :=
  ⟨edgeRight G e, (edge_isLink G e).right_mem⟩

/-- The unordered pair of actual vertices incident with an edge. -/
noncomputable def edgeEnds (e : G.edgeSet) : Sym2 G.vertexSet :=
  s(edgeLeftVertex G e, edgeRightVertex G e)

private theorem isLink_iff_edgeEnds_eq (e : G.edgeSet) (u v : G.vertexSet) :
    G.IsLink e.1 u.1 v.1 ↔ edgeEnds G e = s(u, v) := by
  rw [(edge_isLink G e).isLink_iff]
  simp only [edgeEnds, edgeLeftVertex, edgeRightVertex, Sym2.eq_iff, Subtype.ext_iff]

variable [G.Simple]

/-- Send an edge of a simple multigraph to its unordered pair of endpoints. -/
noncomputable def edgeMap (e : G.edgeSet) : G.toSimpleGraph.edgeSet :=
  ⟨edgeEnds G e, (SimpleGraph.mem_edgeSet G.toSimpleGraph).2 <|
    (Graph.toSimpleGraph_adj_iff (edgeLeftVertex G e) (edgeRightVertex G e)).mpr
      (edge_isLink G e).adj⟩

private theorem edgeMap_injective : Function.Injective (edgeMap G) := by
  intro e f hef
  apply Subtype.ext
  apply (edge_isLink G e).eq
  apply (isLink_iff_edgeEnds_eq G f (edgeLeftVertex G e) (edgeRightVertex G e)).mpr
  change edgeEnds G f = edgeEnds G e
  exact congrArg Subtype.val hef |>.symm

private theorem edgeMap_surjective : Function.Surjective (edgeMap G) := by
  rintro ⟨d, hd⟩
  induction d using Sym2.inductionOn with
  | _ u v =>
    have huv : G.toSimpleGraph.Adj u v := (SimpleGraph.mem_edgeSet G.toSimpleGraph).1 hd
    have huv' : G.Adj u.1 v.1 := (Graph.toSimpleGraph_adj_iff u v).mp huv
    obtain ⟨e, he⟩ := huv'
    let e' : G.edgeSet := ⟨e, he.edge_mem⟩
    refine ⟨e', ?_⟩
    apply Subtype.ext
    change edgeEnds G e' = s(u, v)
    exact (isLink_iff_edgeEnds_eq G e' u v).mp he

/-- The edge bijection from a simple multigraph to its underlying simple graph. -/
noncomputable def edgeEquiv : G.edgeSet ≃ G.toSimpleGraph.edgeSet :=
  Equiv.ofBijective (edgeMap G) ⟨edgeMap_injective G, edgeMap_surjective G⟩

private theorem edgeEquiv_apply_val (e : G.edgeSet) :
    (edgeEquiv G e).1 = edgeEnds G e := rfl

/--
---
conclusion: Lax683916.MultigraphRepresentation.exists_simpleGraph_representation
---
The representing graph has the actual vertices of the multigraph as its
vertex type and joins two vertices exactly when the multigraph does.

# Proof strategy

Use mathlib's `Graph.toSimpleGraph`. Every multigraph edge is sent to its
unordered pair of endpoints. Looplessness makes this pair an edge of the
simple graph; simplicity makes the map injective; and the definition of
adjacency makes it surjective. The identity vertex equivalence and this edge
equivalence preserve incidence.

# Attribution

Direct completion of the correspondence described in
`Mathlib.Combinatorics.Graph.Simple`.
-/
theorem exists_simpleGraph_representation {α : Type u} {β : Type v}
    (G : Graph α β) [G.Simple] :
    ∃ H : SimpleGraph G.vertexSet, Nonempty (IsomorphicToSimpleGraph G H) := by
  refine ⟨G.toSimpleGraph, ⟨{
    vertexEquiv := Equiv.refl _
    edgeEquiv := edgeEquiv G
    map_isLink := ?_ }⟩⟩
  intro e u v
  change G.IsLink e.1 u.1 v.1 ↔ (edgeEquiv G e).1 = s(u, v)
  rw [edgeEquiv_apply_val]
  exact isLink_iff_edgeEnds_eq G e u v

end Lax683916Proofs.MultigraphRepresentation
