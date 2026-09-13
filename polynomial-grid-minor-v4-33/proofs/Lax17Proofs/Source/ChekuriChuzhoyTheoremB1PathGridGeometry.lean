import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1OrderedBlocks

namespace Lax17Proofs

universe u v w

/-!
# Turning ordered corridor rows and columns into a grid certificate

This is the source-faithful terminal construction in Appendix B.1.  Rows and
columns are pairwise disjoint within their own families, every intersection is
a path, and the intersection blocks occur in index order on every row and
column.  The intervening path segments are therefore legitimate grid-edge
connectors.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {g : ℕ}

/-- The final row-column geometry after bump, cross, and hill elimination. -/
structure OrderedPathGridGeometry
    (G : _root_.SimpleGraph V) (g : ℕ) where
  row : Fin g → GraphPath G
  column : Fin g → GraphPath G
  row_nodeDisjoint :
    ∀ ⦃i k : Fin g⦄, i ≠ k → (row i).NodeDisjoint (row k)
  column_nodeDisjoint :
    ∀ ⦃j l : Fin g⦄, j ≠ l → (column j).NodeDisjoint (column l)
  intersectionPath : Fin g → Fin g → GraphPath G
  intersectionPath_vertexSet :
    ∀ i j,
      (intersectionPath i j).vertexSet =
        (row i).vertexSet ∩ (column j).vertexSet
  rowBlocks : ∀ i : Fin g, OrderedPathBlockFamily (row i) g
  rowBlocks_block :
    ∀ i j,
      (rowBlocks i).block j =
        (row i).vertexSet ∩ (column j).vertexSet
  columnBlocks : ∀ j : Fin g, OrderedPathBlockFamily (column j) g
  columnBlocks_block :
    ∀ j i,
      (columnBlocks j).block i =
        (row i).vertexSet ∩ (column j).vertexSet

namespace OrderedPathGridGeometry

/-- Intersection branch set for the canonical grid vertex `(i,j)`. -/
noncomputable def branchSet
    (D : OrderedPathGridGeometry G g) (x : GridVertex g) : Finset V :=
  (D.row x.1).vertexSet ∩ (D.column x.2).vertexSet

theorem branchSet_nonempty
    (D : OrderedPathGridGeometry G g) (x : GridVertex g) :
    (D.branchSet x).Nonempty := by
  unfold branchSet
  rw [← D.rowBlocks_block x.1 x.2]
  rcases (D.rowBlocks x.1).meets x.2 with ⟨v, hv⟩
  exact ⟨v, (Finset.mem_inter.mp hv).2⟩

theorem branchSet_connected
    (D : OrderedPathGridGeometry G g) (x : GridVertex g) :
    (G.induce {v : V | v ∈ D.branchSet x}).Connected := by
  have hset :
      (↑(D.intersectionPath x.1 x.2).vertexSet : Set V) =
        {v : V | v ∈ D.branchSet x} := by
    ext v
    simp [D.intersectionPath_vertexSet, branchSet]
  rw [← hset]
  exact GraphPath.connected_induce_vertexSet _

theorem branchSet_disjoint
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint (D.branchSet x) (D.branchSet y) := by
  classical
  by_cases hrow : x.1 = y.1
  · have hcol : x.2 ≠ y.2 := by
      intro hcol
      exact hxy (Prod.ext hrow hcol)
    exact Disjoint.mono
      (by intro v hv; exact (Finset.mem_inter.mp hv).2)
      (by intro v hv; exact (Finset.mem_inter.mp hv).2)
      (by simpa [GraphPath.NodeDisjoint] using
        D.column_nodeDisjoint hcol)
  · exact Disjoint.mono
      (by intro v hv; exact (Finset.mem_inter.mp hv).1)
      (by intro v hv; exact (Finset.mem_inter.mp hv).1)
      (by simpa [GraphPath.NodeDisjoint] using
        D.row_nodeDisjoint hrow)

/-- A grid edge between vertices in the same row has consecutive column
coordinates. -/
theorem horizontalConsecutive_of_row_eq
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (hrow : x.1 = y.1) :
    FinConsecutive x.2 y.2 := by
  rcases hxy with h | h
  · exact h.2
  · exfalso
    exact (FinConsecutive.irrefl x.1) (by simpa [hrow] using h.2)

/-- A grid edge not lying in one row has consecutive row coordinates and
equal column coordinates. -/
theorem verticalData_of_row_ne
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (hrow : x.1 ≠ y.1) :
    x.2 = y.2 ∧ FinConsecutive x.1 y.1 := by
  rcases hxy with h | h
  · exact False.elim (hrow h.1)
  · exact h

/-- The row or column segment assigned to an oriented canonical-grid edge. -/
noncomputable def connectorPath
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    GraphPath G :=
  if hrow : x.1 = y.1 then
    (D.rowBlocks x.1).connector
      (horizontalConsecutive_of_row_eq hxy hrow)
  else
    (D.columnBlocks x.2).connector
      (verticalData_of_row_ne hxy hrow).2

theorem connectorPath_eq_horizontal
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (hrow : x.1 = y.1) :
    D.connectorPath hxy =
      (D.rowBlocks x.1).connector
        (horizontalConsecutive_of_row_eq hxy hrow) := by
  simp [connectorPath, hrow]

theorem connectorPath_eq_vertical
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (hrow : x.1 ≠ y.1) :
    D.connectorPath hxy =
      (D.columnBlocks x.2).connector
        (verticalData_of_row_ne hxy hrow).2 := by
  simp [connectorPath, hrow]

theorem connectorPath_source_mem
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    (D.connectorPath hxy).source ∈ D.branchSet x := by
  by_cases hrow : x.1 = y.1
  · rw [D.connectorPath_eq_horizontal hxy hrow]
    have hmem := (D.rowBlocks x.1).connector_source_mem
      (horizontalConsecutive_of_row_eq hxy hrow)
    rw [D.rowBlocks_block] at hmem
    simpa [branchSet] using hmem
  · rw [D.connectorPath_eq_vertical hxy hrow]
    have hmem := (D.columnBlocks x.2).connector_source_mem
      (verticalData_of_row_ne hxy hrow).2
    rw [D.columnBlocks_block] at hmem
    simpa [branchSet, Finset.inter_comm] using hmem

theorem connectorPath_target_mem
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    (D.connectorPath hxy).target ∈ D.branchSet y := by
  by_cases hrow : x.1 = y.1
  · rw [D.connectorPath_eq_horizontal hxy hrow]
    have hmem := (D.rowBlocks x.1).connector_target_mem
      (horizontalConsecutive_of_row_eq hxy hrow)
    rw [D.rowBlocks_block] at hmem
    simpa [branchSet, hrow] using hmem
  · rw [D.connectorPath_eq_vertical hxy hrow]
    have hdata := verticalData_of_row_ne hxy hrow
    have hmem := (D.columnBlocks x.2).connector_target_mem hdata.2
    rw [D.columnBlocks_block] at hmem
    simpa [branchSet, hdata.1, Finset.inter_comm] using hmem

theorem connectorPath_vertexSet_subset_row_of_horizontal
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hrow : x.1 = y.1)
    (hcols : FinConsecutive x.2 y.2) :
    (D.connectorPath (Or.inl ⟨hrow, hcols⟩)).vertexSet ⊆
      (D.row x.1).vertexSet := by
  rw [D.connectorPath_eq_horizontal _ hrow]
  exact (D.rowBlocks x.1).connector_vertexSet_subset _

theorem connectorPath_vertexSet_subset_column_of_vertical
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hcol : x.2 = y.2)
    (hrows : FinConsecutive x.1 y.1) :
    (D.connectorPath (Or.inr ⟨hcol, hrows⟩)).vertexSet ⊆
      (D.column x.2).vertexSet := by
  have hrow : x.1 ≠ y.1 := by
    intro hr
    exact (FinConsecutive.irrefl x.1) (by simpa [hr] using hrows)
  rw [D.connectorPath_eq_vertical _ hrow]
  exact (D.columnBlocks x.2).connector_vertexSet_subset _

theorem connectorPath_internal_disjoint_branch
    (D : OrderedPathGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (z : GridVertex g) :
    Disjoint (gridConnectorInterior (D.connectorPath hxy))
      (D.branchSet z) := by
  classical
  by_cases hrow : x.1 = y.1
  · rw [D.connectorPath_eq_horizontal hxy hrow]
    let hcols := horizontalConsecutive_of_row_eq hxy hrow
    by_cases hrz : x.1 = z.1
    · have hdisj :=
        (D.rowBlocks x.1).connector_interior_disjoint_block hcols z.2
      rw [D.rowBlocks_block] at hdisj
      simpa [branchSet, hrz] using hdisj
    · exact Disjoint.mono
        ((D.rowBlocks x.1).connector_interior_subset_path hcols)
        (by intro v hv; exact (Finset.mem_inter.mp hv).1)
        (by simpa [GraphPath.NodeDisjoint] using
          D.row_nodeDisjoint hrz)
  · rw [D.connectorPath_eq_vertical hxy hrow]
    let hdata := verticalData_of_row_ne hxy hrow
    by_cases hcz : x.2 = z.2
    · have hdisj :=
        (D.columnBlocks x.2).connector_interior_disjoint_block hdata.2 z.1
      rw [D.columnBlocks_block] at hdisj
      simpa [branchSet, hcz, Finset.inter_comm] using hdisj
    · exact Disjoint.mono
        ((D.columnBlocks x.2).connector_interior_subset_path hdata.2)
        (by intro v hv; exact (Finset.mem_inter.mp hv).2)
        (by simpa [GraphPath.NodeDisjoint] using
          D.column_nodeDisjoint hcz)

/-- Two rank-increasing oriented grid edges cannot be reversals of one
another. -/
theorem gridVertexPair_ne_reverse_of_rank_lt
    {x y z t : GridVertex g}
    (hxy : gridVertexAllocationRank x < gridVertexAllocationRank y)
    (hzt : gridVertexAllocationRank z < gridVertexAllocationRank t) :
    (x, y) ≠ (t, z) := by
  intro h
  have hxt : x = t := congrArg Prod.fst h
  have hyz : y = z := congrArg Prod.snd h
  subst t
  subst z
  omega

theorem connectorPath_pairwise_internal_disjoint
    (D : OrderedPathGridGeometry G g)
    {x y z t : GridVertex g}
    (hxy : (gridGraph g).Adj x y)
    (hzt : (gridGraph g).Adj z t)
    (hrankXY :
      gridVertexAllocationRank x < gridVertexAllocationRank y)
    (hrankZT :
      gridVertexAllocationRank z < gridVertexAllocationRank t)
    (hpairs : (x, y) ≠ (z, t)) :
    Disjoint
      (gridConnectorInterior (D.connectorPath hxy))
      (gridConnectorInterior (D.connectorPath hzt)) := by
  classical
  by_cases hxyrow : x.1 = y.1
  · let hxycols := horizontalConsecutive_of_row_eq hxy hxyrow
    rw [D.connectorPath_eq_horizontal hxy hxyrow]
    by_cases hztrow : z.1 = t.1
    · let hztcols := horizontalConsecutive_of_row_eq hzt hztrow
      rw [D.connectorPath_eq_horizontal hzt hztrow]
      by_cases hxzrow : x.1 = z.1
      · rw [← hxzrow]
        apply (D.rowBlocks x.1).connector_pairwise_interior_disjoint
          hxycols hztcols
        · intro hcols
          apply hpairs
          have hxz : x = z := Prod.ext hxzrow (congrArg Prod.fst hcols)
          have hytRow : y.1 = t.1 :=
            hxyrow.symm.trans (hxzrow.trans hztrow)
          have hytCol : y.2 = t.2 := by
            have hp :
                x.2 = z.2 ∧ y.2 = t.2 := by
              simpa only [Prod.mk.injEq] using hcols
            exact hp.2
          have hyt : y = t :=
            Prod.ext hytRow hytCol
          exact Prod.ext hxz hyt
        · intro hcols
          apply gridVertexPair_ne_reverse_of_rank_lt hrankXY hrankZT
          have hxtRow : x.1 = t.1 := hxzrow.trans hztrow
          have hxt : x = t :=
            Prod.ext hxtRow (congrArg Prod.fst hcols)
          have hyzRow : y.1 = z.1 := hxyrow.symm.trans hxzrow
          have hyzCol : y.2 = z.2 := by
            have hp :
                x.2 = t.2 ∧ y.2 = z.2 := by
              simpa only [Prod.mk.injEq] using hcols
            exact hp.2
          have hyz : y = z :=
            Prod.ext hyzRow hyzCol
          exact Prod.ext hxt hyz
      · exact Disjoint.mono
          ((D.rowBlocks x.1).connector_interior_subset_path hxycols)
          ((D.rowBlocks z.1).connector_interior_subset_path hztcols)
          (by simpa [GraphPath.NodeDisjoint] using
            D.row_nodeDisjoint hxzrow)
    · let hztdata := verticalData_of_row_ne hzt hztrow
      rw [D.connectorPath_eq_vertical hzt hztrow]
      rw [Finset.disjoint_left]
      intro v hvhorizontal hvvertical
      have hvrow :
          v ∈ (D.row x.1).vertexSet :=
        (D.rowBlocks x.1).connector_interior_subset_path hxycols
          hvhorizontal
      have hvcolumn :
          v ∈ (D.column z.2).vertexSet :=
        (D.columnBlocks z.2).connector_interior_subset_path hztdata.2
          hvvertical
      have hvblock :
          v ∈ (D.columnBlocks z.2).block x.1 := by
        rw [D.columnBlocks_block]
        exact Finset.mem_inter.mpr ⟨hvrow, hvcolumn⟩
      exact
        (Finset.disjoint_left.mp
          ((D.columnBlocks z.2).connector_interior_disjoint_block
            hztdata.2 x.1))
          hvvertical hvblock
  · let hxydata := verticalData_of_row_ne hxy hxyrow
    rw [D.connectorPath_eq_vertical hxy hxyrow]
    by_cases hztrow : z.1 = t.1
    · let hztcols := horizontalConsecutive_of_row_eq hzt hztrow
      rw [D.connectorPath_eq_horizontal hzt hztrow]
      rw [Finset.disjoint_left]
      intro v hvvertical hvhorizontal
      have hvcolumn :
          v ∈ (D.column x.2).vertexSet :=
        (D.columnBlocks x.2).connector_interior_subset_path hxydata.2
          hvvertical
      have hvrow :
          v ∈ (D.row z.1).vertexSet :=
        (D.rowBlocks z.1).connector_interior_subset_path hztcols
          hvhorizontal
      have hvblock :
          v ∈ (D.columnBlocks x.2).block z.1 := by
        rw [D.columnBlocks_block]
        exact Finset.mem_inter.mpr ⟨hvrow, hvcolumn⟩
      exact
        (Finset.disjoint_left.mp
          ((D.columnBlocks x.2).connector_interior_disjoint_block
            hxydata.2 z.1))
          hvvertical hvblock
    · let hztdata := verticalData_of_row_ne hzt hztrow
      rw [D.connectorPath_eq_vertical hzt hztrow]
      by_cases hxzcol : x.2 = z.2
      · have hordered_ne : (x.1, y.1) ≠ (z.1, t.1) := by
          intro hrows
          apply hpairs
          have hp :
              x.1 = z.1 ∧ y.1 = t.1 := by
            simpa only [Prod.mk.injEq] using hrows
          have hxz : x = z := Prod.ext hp.1 hxzcol
          have hytCol : y.2 = t.2 :=
            hxydata.1.symm.trans (hxzcol.trans hztdata.1)
          have hyt : y = t := Prod.ext hp.2 hytCol
          exact Prod.ext hxz hyt
        have hreversed_ne : (x.1, y.1) ≠ (t.1, z.1) := by
          intro hrows
          apply gridVertexPair_ne_reverse_of_rank_lt hrankXY hrankZT
          have hp :
              x.1 = t.1 ∧ y.1 = z.1 := by
            simpa only [Prod.mk.injEq] using hrows
          have hxtCol : x.2 = t.2 :=
            hxzcol.trans hztdata.1
          have hxt : x = t := Prod.ext hp.1 hxtCol
          have hyzCol : y.2 = z.2 :=
            hxydata.1.symm.trans hxzcol
          have hyz : y = z := Prod.ext hp.2 hyzCol
          exact Prod.ext hxt hyz
        exact indexedConnector_pairwise_interior_disjoint
          D.columnBlocks hxzcol hxydata.2 hztdata.2
          hordered_ne hreversed_ne
      · exact Disjoint.mono
          ((D.columnBlocks x.2).connector_interior_subset_path hxydata.2)
          ((D.columnBlocks z.2).connector_interior_subset_path hztdata.2)
          (by simpa [GraphPath.NodeDisjoint] using
            D.column_nodeDisjoint hxzcol)

/-- The ordered row-column geometry is exactly the concrete connector
certificate consumed by the minor assembly theorem. -/
noncomputable def toGridConnectorAssemblyCertificate
    (D : OrderedPathGridGeometry G g) :
    GridConnectorAssemblyCertificate G g where
  branchSet := D.branchSet
  branch_nonempty := D.branchSet_nonempty
  branch_connected := D.branchSet_connected
  branch_disjoint := by
    intro x y hxy
    exact D.branchSet_disjoint hxy
  connectorPath := by
    intro x y hxy
    exact D.connectorPath hxy
  connector_source_mem := by
    intro x y hxy
    exact D.connectorPath_source_mem hxy
  connector_target_mem := by
    intro x y hxy
    exact D.connectorPath_target_mem hxy
  connector_internal_disjoint_branch := by
    intro x y hxy z
    exact D.connectorPath_internal_disjoint_branch hxy z
  connector_pairwise_internal_disjoint := by
    intro x y z t hxy hzt hrankXY hrankZT hpairs
    exact D.connectorPath_pairwise_internal_disjoint
      hxy hzt hrankXY hrankZT hpairs

theorem containsGridMinor (D : OrderedPathGridGeometry G g) :
    ContainsGridMinor G g :=
  D.toGridConnectorAssemblyCertificate.containsGridMinor

end OrderedPathGridGeometry

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
