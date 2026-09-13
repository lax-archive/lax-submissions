import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1

namespace Lax17Proofs

universe u v w

/-!
# Appendix B.1 terminal grid assembly

This module isolates the minor-theoretic last step of Chekuri--Chuzhoy
Appendix B.1.  The row-column intersections are already nonempty, connected,
and pairwise disjoint.  Every horizontal or vertical grid edge is represented
by a host path whose internal vertices avoid all intersection branch sets, and
the chosen connector paths are pairwise internally disjoint.

The proof allocates the drop-last part of every connector to one endpoint.
This turns path connections between the original intersections into literal
adjacencies between connected, pairwise-disjoint enlarged branch sets.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {g : ℕ}

/-- Internal vertices of a connector path. -/
noncomputable def gridConnectorInterior (P : GraphPath G) : Finset V :=
  (P.vertexSet.erase P.source).erase P.target

/-- A fixed injective rank on the finite canonical-grid vertex type.  It is
used only to choose one orientation of every undirected grid edge. -/
noncomputable def gridVertexAllocationRank (x : GridVertex g) : ℕ :=
  ((Fintype.equivFin (GridVertex g)) x).1

theorem gridVertexAllocationRank_injective :
    Function.Injective (gridVertexAllocationRank (g := g)) := by
  intro x y hxy
  apply (Fintype.equivFin (GridVertex g)).injective
  exact Fin.ext hxy

theorem gridVertexAllocationRank_lt_or_gt_of_ne
    {x y : GridVertex g} (hxy : x ≠ y) :
    gridVertexAllocationRank x < gridVertexAllocationRank y ∨
      gridVertexAllocationRank y < gridVertexAllocationRank x := by
  have hrank_ne :
      gridVertexAllocationRank x ≠ gridVertexAllocationRank y := by
    intro hrank
    exact hxy (gridVertexAllocationRank_injective hrank)
  exact lt_or_gt_of_ne hrank_ne

/-- Concrete terminal geometry sufficient to assemble a canonical grid minor.

`branchSet x` is the connected row-column intersection for grid vertex `x`.
For each oriented statement of a canonical grid edge, `connectorPath` supplies
a host path with endpoints in the corresponding two intersections.  Only the
orientation from lower to higher `gridVertexAllocationRank` is used.  Thus the
pairwise-disjointness field is imposed only on those chosen orientations, not
also on the unused reversals. -/
structure GridConnectorAssemblyCertificate
    (G : _root_.SimpleGraph V) (g : ℕ) where
  branchSet : GridVertex g → Finset V
  branch_nonempty :
    ∀ x : GridVertex g, (branchSet x).Nonempty
  branch_connected :
    ∀ x : GridVertex g,
      (G.induce {v : V | v ∈ branchSet x}).Connected
  branch_disjoint :
    ∀ ⦃x y : GridVertex g⦄,
      x ≠ y → Disjoint (branchSet x) (branchSet y)
  connectorPath :
    ∀ ⦃x y : GridVertex g⦄,
      (gridGraph g).Adj x y → GraphPath G
  connector_source_mem :
    ∀ ⦃x y : GridVertex g⦄
      (hxy : (gridGraph g).Adj x y),
        (connectorPath hxy).source ∈ branchSet x
  connector_target_mem :
    ∀ ⦃x y : GridVertex g⦄
      (hxy : (gridGraph g).Adj x y),
        (connectorPath hxy).target ∈ branchSet y
  connector_internal_disjoint_branch :
    ∀ ⦃x y : GridVertex g⦄
      (hxy : (gridGraph g).Adj x y) (z : GridVertex g),
        Disjoint (gridConnectorInterior (connectorPath hxy)) (branchSet z)
  connector_pairwise_internal_disjoint :
    ∀ ⦃x y z t : GridVertex g⦄
      (hxy : (gridGraph g).Adj x y)
      (hzt : (gridGraph g).Adj z t),
        gridVertexAllocationRank x < gridVertexAllocationRank y →
          gridVertexAllocationRank z < gridVertexAllocationRank t →
            (x, y) ≠ (z, t) →
              Disjoint
                (gridConnectorInterior (connectorPath hxy))
                (gridConnectorInterior (connectorPath hzt))

namespace GridConnectorAssemblyCertificate

/-- A vertex in the allocated drop-last part of a nontrivial connector is
either its source or an internal vertex. -/
theorem mem_dropLast_eq_source_or_mem_interior
    (P : GraphPath G) (hne : P.source ≠ P.target) {v : V}
    (hv : v ∈ P.dropLast.vertexSet) :
    v = P.source ∨ v ∈ gridConnectorInterior P := by
  classical
  by_cases hvsource : v = P.source
  · exact Or.inl hvsource
  · right
    have hvVertex : v ∈ P.vertexSet :=
      P.dropLast_vertexSet_subset hv
    have hvtarget : v ≠ P.target := by
      intro hvt
      exact P.target_not_mem_dropLast_vertexSet hne
        (by simpa [hvt] using hv)
    simp [gridConnectorInterior, hvsource, hvtarget, hvVertex]

/-- The endpoints of every connector are distinct because they lie in
different original branch sets. -/
theorem connector_source_ne_target
    (C : GridConnectorAssemblyCertificate G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    (C.connectorPath hxy).source ≠ (C.connectorPath hxy).target := by
  intro hst
  have hsource :
      (C.connectorPath hxy).source ∈ C.branchSet x :=
    C.connector_source_mem hxy
  have htarget :
      (C.connectorPath hxy).source ∈ C.branchSet y := by
    simpa [hst] using C.connector_target_mem hxy
  exact Finset.disjoint_left.mp
    (C.branch_disjoint ((gridGraph g).ne_of_adj hxy))
    hsource htarget

/-- Enlarge an intersection branch set by the drop-last parts of all incident
connector paths oriented outward from that grid vertex. -/
noncomputable def allocatedBranchSet
    (C : GridConnectorAssemblyCertificate G g)
    (x : GridVertex g) : Finset V := by
  classical
  exact
    C.branchSet x ∪
      Finset.univ.biUnion (fun y : GridVertex g =>
        if hxy : (gridGraph g).Adj x y ∧
            gridVertexAllocationRank x < gridVertexAllocationRank y then
          (C.connectorPath hxy.1).dropLast.vertexSet
        else
          ∅)

@[simp] theorem branchSet_subset_allocatedBranchSet
    (C : GridConnectorAssemblyCertificate G g)
    (x : GridVertex g) :
    C.branchSet x ⊆ C.allocatedBranchSet x := by
  classical
  intro v hv
  exact Finset.mem_union_left _ hv

theorem mem_allocatedBranchSet_iff
    (C : GridConnectorAssemblyCertificate G g)
    {x : GridVertex g} {v : V} :
    v ∈ C.allocatedBranchSet x ↔
      v ∈ C.branchSet x ∨
        ∃ (y : GridVertex g)
          (hxy : (gridGraph g).Adj x y),
            gridVertexAllocationRank x < gridVertexAllocationRank y ∧
              v ∈ (C.connectorPath hxy).dropLast.vertexSet := by
  classical
  constructor
  · intro hv
    rw [allocatedBranchSet] at hv
    rw [Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨y, _hy, hvif⟩
      by_cases hcond :
          (gridGraph g).Adj x y ∧
            gridVertexAllocationRank x < gridVertexAllocationRank y
      · exact Or.inr
          ⟨y, hcond.1, hcond.2, by simpa [hcond] using hvif⟩
      · simp [hcond] at hvif
  · intro hv
    rcases hv with hv | hv
    · exact Finset.mem_union_left _ hv
    · rcases hv with ⟨y, hxy, hrank, hvpath⟩
      rw [allocatedBranchSet]
      exact Finset.mem_union_right _ <|
        Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by
          have hcond :
              (gridGraph g).Adj x y ∧
                gridVertexAllocationRank x <
                  gridVertexAllocationRank y :=
            ⟨hxy, hrank⟩
          simpa [hcond] using hvpath⟩

/-- The penultimate vertex of a chosen connector belongs to the allocated
branch set of its lower-ranked endpoint. -/
theorem connector_penultimate_mem_allocatedBranchSet
    (C : GridConnectorAssemblyCertificate G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (hrank :
      gridVertexAllocationRank x < gridVertexAllocationRank y) :
    (C.connectorPath hxy).penultimate ∈ C.allocatedBranchSet x := by
  have hmem :
      (C.connectorPath hxy).penultimate ∈
        (C.connectorPath hxy).dropLast.vertexSet := by
    simpa using
      GraphPath.target_mem_vertexSet ((C.connectorPath hxy).dropLast)
  exact C.mem_allocatedBranchSet_iff.mpr
    (Or.inr ⟨y, hxy, hrank, hmem⟩)

/-- Every allocated branch set is connected.  Its original intersection is a
connected core, and each allocated drop-last path meets that core at its
source. -/
theorem allocatedBranchSet_connected
    (C : GridConnectorAssemblyCertificate G g)
    (x : GridVertex g) :
    (G.induce {v : V | v ∈ C.allocatedBranchSet x}).Connected := by
  classical
  rcases C.branch_nonempty x with ⟨a, ha⟩
  have haAllocated : a ∈ C.allocatedBranchSet x :=
    C.branchSet_subset_allocatedBranchSet x ha
  refine G.induce_connected_of_patches a haAllocated ?_
  intro v hv
  rcases C.mem_allocatedBranchSet_iff.mp hv with hvBranch | hvPath
  · let S : Set V := {w : V | w ∈ C.branchSet x}
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · intro w hw
      exact C.branchSet_subset_allocatedBranchSet x hw
    · exact ha
    · exact hvBranch
    · simpa [S] using
        (C.branch_connected x).preconnected
          ⟨a, ha⟩ ⟨v, hvBranch⟩
  · rcases hvPath with ⟨y, hxy, hrank, hvPath⟩
    let Sbranch : Set V := {w : V | w ∈ C.branchSet x}
    let Spath : Set V :=
      {w : V | w ∈ (C.connectorPath hxy).dropLast.vertexSet}
    let S : Set V := Sbranch ∪ Spath
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases hw with hwBranch | hwPath
      · exact C.branchSet_subset_allocatedBranchSet x hwBranch
      · exact C.mem_allocatedBranchSet_iff.mpr
          (Or.inr ⟨y, hxy, hrank, hwPath⟩)
    · exact Or.inl ha
    · exact Or.inr hvPath
    · have hsourceBranch :
          (C.connectorPath hxy).source ∈ Sbranch := by
        exact C.connector_source_mem hxy
      have hsourcePath :
          (C.connectorPath hxy).source ∈ Spath := by
        simpa [Spath] using
          GraphPath.source_mem_vertexSet
            ((C.connectorPath hxy).dropLast)
      have hconnected : (G.induce S).Connected := by
        simpa [S, Sbranch, Spath] using
          G.induce_union_connected
            (C.branch_connected x).preconnected
            (GraphPath.connected_induce_vertexSet
              ((C.connectorPath hxy).dropLast)).preconnected
            ⟨(C.connectorPath hxy).source,
              hsourceBranch, hsourcePath⟩
      exact hconnected.preconnected
        ⟨a, Or.inl ha⟩ ⟨v, Or.inr hvPath⟩

/-- An original branch set different from the source branch is disjoint from
the drop-last part of a chosen connector. -/
theorem branchSet_disjoint_connector_dropLast_of_ne_source
    (C : GridConnectorAssemblyCertificate G g)
    {x y z : GridVertex g}
    (hxy : (gridGraph g).Adj x y) (hzx : z ≠ x) :
    Disjoint (C.branchSet z)
      (C.connectorPath hxy).dropLast.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvBranch hvPath
  rcases mem_dropLast_eq_source_or_mem_interior
      (C.connectorPath hxy) (C.connector_source_ne_target hxy) hvPath with
    hvSource | hvInterior
  · have hvSourceBranch : v ∈ C.branchSet x := by
      simpa [hvSource] using C.connector_source_mem hxy
    exact Finset.disjoint_left.mp (C.branch_disjoint hzx)
      hvBranch hvSourceBranch
  · exact Finset.disjoint_left.mp
      (C.connector_internal_disjoint_branch hxy z).symm
      hvBranch hvInterior

/-- Drop-last parts allocated to different source grid vertices are disjoint.
The proof is the four-way endpoint/internal-vertex split. -/
theorem connector_dropLast_disjoint_of_source_ne
    (C : GridConnectorAssemblyCertificate G g)
    {x y z t : GridVertex g}
    (hxy : (gridGraph g).Adj x y)
    (hzt : (gridGraph g).Adj z t)
    (hrankXY :
      gridVertexAllocationRank x < gridVertexAllocationRank y)
    (hrankZT :
      gridVertexAllocationRank z < gridVertexAllocationRank t)
    (hxz : x ≠ z) :
    Disjoint
      (C.connectorPath hxy).dropLast.vertexSet
      (C.connectorPath hzt).dropLast.vertexSet := by
  classical
  rw [Finset.disjoint_left]
  intro v hvXY hvZT
  rcases mem_dropLast_eq_source_or_mem_interior
      (C.connectorPath hxy) (C.connector_source_ne_target hxy) hvXY with
    hvSourceXY | hvInteriorXY
  · rcases mem_dropLast_eq_source_or_mem_interior
        (C.connectorPath hzt) (C.connector_source_ne_target hzt) hvZT with
      hvSourceZT | hvInteriorZT
    · have hvBranchX : v ∈ C.branchSet x := by
        simpa [hvSourceXY] using C.connector_source_mem hxy
      have hvBranchZ : v ∈ C.branchSet z := by
        simpa [hvSourceZT] using C.connector_source_mem hzt
      exact Finset.disjoint_left.mp (C.branch_disjoint hxz)
        hvBranchX hvBranchZ
    · have hvBranchX : v ∈ C.branchSet x := by
        simpa [hvSourceXY] using C.connector_source_mem hxy
      exact Finset.disjoint_left.mp
        (C.connector_internal_disjoint_branch hzt x).symm
        hvBranchX hvInteriorZT
  · rcases mem_dropLast_eq_source_or_mem_interior
        (C.connectorPath hzt) (C.connector_source_ne_target hzt) hvZT with
      hvSourceZT | hvInteriorZT
    · have hvBranchZ : v ∈ C.branchSet z := by
        simpa [hvSourceZT] using C.connector_source_mem hzt
      exact Finset.disjoint_left.mp
        (C.connector_internal_disjoint_branch hxy z)
        hvInteriorXY hvBranchZ
    · have hpairs : (x, y) ≠ (z, t) := by
        intro hpairs
        exact hxz (congrArg Prod.fst hpairs)
      exact Finset.disjoint_left.mp
        (C.connector_pairwise_internal_disjoint
          hxy hzt hrankXY hrankZT hpairs)
        hvInteriorXY hvInteriorZT

/-- Distinct allocated branch sets are disjoint. -/
theorem allocatedBranchSet_disjoint
    (C : GridConnectorAssemblyCertificate G g)
    {x z : GridVertex g} (hxz : x ≠ z) :
    Disjoint (C.allocatedBranchSet x) (C.allocatedBranchSet z) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvX hvZ
  rcases C.mem_allocatedBranchSet_iff.mp hvX with
    hvBranchX | hvPathX
  · rcases C.mem_allocatedBranchSet_iff.mp hvZ with
      hvBranchZ | hvPathZ
    · exact Finset.disjoint_left.mp (C.branch_disjoint hxz)
        hvBranchX hvBranchZ
    · rcases hvPathZ with ⟨t, hzt, _hrankZT, hvZT⟩
      exact Finset.disjoint_left.mp
        (C.branchSet_disjoint_connector_dropLast_of_ne_source hzt hxz)
        hvBranchX hvZT
  · rcases hvPathX with ⟨y, hxy, hrankXY, hvXY⟩
    rcases C.mem_allocatedBranchSet_iff.mp hvZ with
      hvBranchZ | hvPathZ
    · exact Finset.disjoint_left.mp
        (C.branchSet_disjoint_connector_dropLast_of_ne_source
          hxy hxz.symm).symm
        hvXY hvBranchZ
    · rcases hvPathZ with ⟨t, hzt, hrankZT, hvZT⟩
      exact Finset.disjoint_left.mp
        (C.connector_dropLast_disjoint_of_source_ne
          hxy hzt hrankXY hrankZT hxz)
        hvXY hvZT

/-- Every canonical grid edge is witnessed by a host edge between the
allocated branch sets. -/
theorem allocatedBranchSet_adjacent
    (C : GridConnectorAssemblyCertificate G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    ∃ u ∈ C.allocatedBranchSet x,
      ∃ v ∈ C.allocatedBranchSet y, G.Adj u v := by
  rcases gridVertexAllocationRank_lt_or_gt_of_ne
      ((gridGraph g).ne_of_adj hxy) with hrank | hrank
  · refine
      ⟨(C.connectorPath hxy).penultimate,
        C.connector_penultimate_mem_allocatedBranchSet hxy hrank,
        (C.connectorPath hxy).target,
        C.branchSet_subset_allocatedBranchSet y
          (C.connector_target_mem hxy), ?_⟩
    exact (C.connectorPath hxy).penultimate_adj_target
      (C.connector_source_ne_target hxy)
  · have hyx : (gridGraph g).Adj y x := (gridGraph g).symm hxy
    refine
      ⟨(C.connectorPath hyx).target,
        C.branchSet_subset_allocatedBranchSet x
          (C.connector_target_mem hyx),
        (C.connectorPath hyx).penultimate,
        C.connector_penultimate_mem_allocatedBranchSet hyx hrank, ?_⟩
    exact G.symm <|
      (C.connectorPath hyx).penultimate_adj_target
        (C.connector_source_ne_target hyx)

/-- The concrete intersection-and-connector geometry gives a standard minor
model of the canonical grid. -/
noncomputable def toMinorModel
    (C : GridConnectorAssemblyCertificate G g) :
    MinorModel (gridGraph g) G where
  branchSet := C.allocatedBranchSet
  branch_nonempty := by
    intro x
    rcases C.branch_nonempty x with ⟨v, hv⟩
    exact ⟨v, C.branchSet_subset_allocatedBranchSet x hv⟩
  branch_connected := C.allocatedBranchSet_connected
  branch_disjoint := by
    intro x y hxy
    exact C.allocatedBranchSet_disjoint hxy
  adjacent := by
    intro x y hxy
    exact C.allocatedBranchSet_adjacent hxy

/-- Connected pairwise-disjoint row-column intersections joined by internally
disjoint horizontal and vertical connector paths contain the canonical
`g x g` grid as a minor. -/
theorem containsGridMinor
    (C : GridConnectorAssemblyCertificate G g) :
    ContainsGridMinor G g :=
  ContainsGridMinor.of_gridGraph_model C.toMinorModel

end GridConnectorAssemblyCertificate

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
