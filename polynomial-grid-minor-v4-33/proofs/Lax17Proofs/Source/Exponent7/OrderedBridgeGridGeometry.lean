import Lax17Proofs.Source.Exponent7.CleanMatchingDichotomy
import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1PathGridGeometry

namespace Lax17Proofs

/-!
# Grid assembly from batched vertical bridges

For each column block, the short-wide construction provides one simultaneous
bridge for every consecutive pair of selected rows. These bridges determine a
grid minor.

The branch sets are connected, ordered blocks on the horizontal rows.
Horizontal connectors are the intervening segments supplied by
`OrderedPathBlockFamily`; vertical connectors are the prescribed bridge
paths.
-/

namespace SimpleGraph
namespace Exponent7

open ChekuriChuzhoy AppendixB1

universe u

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {g : ℕ}

/-- Ordered horizontal rows and simultaneous vertical bridges sufficient for
a `g x g` grid minor. -/
structure OrderedBridgeGridGeometry
    (G : _root_.SimpleGraph V) (g : ℕ) where
  row : Fin g → GraphPath G
  row_nodeDisjoint :
    ∀ ⦃i j : Fin g⦄, i ≠ j → (row i).NodeDisjoint (row j)
  block : ∀ i : Fin g, OrderedPathBlockFamily (row i) g
  block_connected :
    ∀ i j,
      (G.induce {v : V | v ∈ (block i).block j}).Connected
  verticalPath :
    ∀ ⦃x y : GridVertex g⦄,
      x.2 = y.2 → FinConsecutive x.1 y.1 → GraphPath G
  vertical_source_mem :
    ∀ ⦃x y : GridVertex g⦄
      (hcol : x.2 = y.2) (hrows : FinConsecutive x.1 y.1),
        (verticalPath hcol hrows).source ∈ (block x.1).block x.2
  vertical_target_mem :
    ∀ ⦃x y : GridVertex g⦄
      (hcol : x.2 = y.2) (hrows : FinConsecutive x.1 y.1),
        (verticalPath hcol hrows).target ∈ (block y.1).block y.2
  vertical_interior_disjoint_row :
    ∀ ⦃x y : GridVertex g⦄
      (hcol : x.2 = y.2) (hrows : FinConsecutive x.1 y.1)
      (r : Fin g),
        Disjoint
          (gridConnectorInterior (verticalPath hcol hrows))
          (row r).vertexSet
  vertical_pairwise_interior_disjoint :
    ∀ ⦃x y z t : GridVertex g⦄
      (hxyCol : x.2 = y.2) (hxyRows : FinConsecutive x.1 y.1)
      (hztCol : z.2 = t.2) (hztRows : FinConsecutive z.1 t.1),
        (x, y) ≠ (z, t) →
        (x, y) ≠ (t, z) →
          Disjoint
            (gridConnectorInterior (verticalPath hxyCol hxyRows))
            (gridConnectorInterior (verticalPath hztCol hztRows))

namespace OrderedBridgeGridGeometry

/-- The branch set assigned to grid vertex `(row,column)`. -/
noncomputable def branchSet
    (D : OrderedBridgeGridGeometry G g) (x : GridVertex g) : Finset V :=
  (D.block x.1).block x.2

theorem branchSet_nonempty
    (D : OrderedBridgeGridGeometry G g) (x : GridVertex g) :
    (D.branchSet x).Nonempty := by
  rcases (D.block x.1).meets x.2 with ⟨v, hv⟩
  exact ⟨v, (Finset.mem_inter.mp hv).2⟩

theorem branchSet_connected
    (D : OrderedBridgeGridGeometry G g) (x : GridVertex g) :
    (G.induce {v : V | v ∈ D.branchSet x}).Connected :=
  D.block_connected x.1 x.2

theorem branchSet_disjoint
    (D : OrderedBridgeGridGeometry G g)
    {x y : GridVertex g} (hxy : x ≠ y) :
    Disjoint (D.branchSet x) (D.branchSet y) := by
  classical
  by_cases hrow : x.1 = y.1
  · have hcol : x.2 ≠ y.2 := by
      intro hcol
      exact hxy (Prod.ext hrow hcol)
    change Disjoint
      ((D.block x.1).block x.2)
      ((D.block y.1).block y.2)
    rw [← hrow]
    exact (D.block x.1).pairwise_disjoint hcol
  · apply Disjoint.mono
      ((D.block x.1).block_subset x.2)
      ((D.block y.1).block_subset y.2)
    simpa [GraphPath.NodeDisjoint] using D.row_nodeDisjoint hrow

/-- Connector selected for an oriented canonical-grid edge. -/
noncomputable def connectorPath
    (D : OrderedBridgeGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    GraphPath G :=
  if hrow : x.1 = y.1 then
    (D.block x.1).connector
      (ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
        hxy hrow)
  else
    let hdata :=
      ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.verticalData_of_row_ne
        hxy hrow
    D.verticalPath hdata.1 hdata.2

theorem connectorPath_eq_horizontal
    (D : OrderedBridgeGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (hrow : x.1 = y.1) :
    D.connectorPath hxy =
      (D.block x.1).connector
        (ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
          hxy hrow) := by
  simp [connectorPath, hrow]

theorem connectorPath_eq_vertical
    (D : OrderedBridgeGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (hrow : x.1 ≠ y.1) :
    D.connectorPath hxy =
      D.verticalPath
        (ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.verticalData_of_row_ne
          hxy hrow).1
        (ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.verticalData_of_row_ne
          hxy hrow).2 := by
  simp [connectorPath, hrow]

theorem connectorPath_source_mem
    (D : OrderedBridgeGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    (D.connectorPath hxy).source ∈ D.branchSet x := by
  by_cases hrow : x.1 = y.1
  · rw [D.connectorPath_eq_horizontal hxy hrow]
    exact (D.block x.1).connector_source_mem _
  · rw [D.connectorPath_eq_vertical hxy hrow]
    exact D.vertical_source_mem _ _

theorem connectorPath_target_mem
    (D : OrderedBridgeGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y) :
    (D.connectorPath hxy).target ∈ D.branchSet y := by
  by_cases hrow : x.1 = y.1
  · rw [D.connectorPath_eq_horizontal hxy hrow]
    have hmem := (D.block x.1).connector_target_mem
      (ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
        hxy hrow)
    change
      ((D.block x.1).connector
        (ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
          hxy hrow)).target ∈
        (D.block y.1).block y.2
    rw [← hrow]
    exact hmem
  · rw [D.connectorPath_eq_vertical hxy hrow]
    exact D.vertical_target_mem _ _

theorem connectorPath_internal_disjoint_branch
    (D : OrderedBridgeGridGeometry G g)
    {x y : GridVertex g} (hxy : (gridGraph g).Adj x y)
    (z : GridVertex g) :
    Disjoint (gridConnectorInterior (D.connectorPath hxy))
      (D.branchSet z) := by
  classical
  by_cases hrow : x.1 = y.1
  · rw [D.connectorPath_eq_horizontal hxy hrow]
    let hcols :=
      ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
        hxy hrow
    by_cases hrz : x.1 = z.1
    · have hdisj :=
        (D.block x.1).connector_interior_disjoint_block hcols z.2
      change Disjoint
        (gridConnectorInterior ((D.block x.1).connector hcols))
        ((D.block z.1).block z.2)
      rw [← hrz]
      exact hdisj
    · apply Disjoint.mono
        ((D.block x.1).connector_interior_subset_path hcols)
        ((D.block z.1).block_subset z.2)
      simpa [GraphPath.NodeDisjoint] using D.row_nodeDisjoint hrz
  · rw [D.connectorPath_eq_vertical hxy hrow]
    apply Disjoint.mono_right ((D.block z.1).block_subset z.2)
    exact D.vertical_interior_disjoint_row _ _ z.1

theorem connectorPath_pairwise_internal_disjoint
    (D : OrderedBridgeGridGeometry G g)
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
  by_cases hxyRow : x.1 = y.1
  · rw [D.connectorPath_eq_horizontal hxy hxyRow]
    let hxyCols :=
      ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
        hxy hxyRow
    by_cases hztRow : z.1 = t.1
    · rw [D.connectorPath_eq_horizontal hzt hztRow]
      let hztCols :=
        ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
          hzt hztRow
      by_cases hxz : x.1 = z.1
      · rw [← hxz]
        apply (D.block x.1).connector_pairwise_interior_disjoint
          hxyCols hztCols
        · intro hcols
          apply hpairs
          have hxz' : x = z :=
            Prod.ext hxz (congrArg Prod.fst hcols)
          have hytRow : y.1 = t.1 :=
            hxyRow.symm.trans (hxz.trans hztRow)
          have hytCol : y.2 = t.2 := by
            have hp :
                x.2 = z.2 ∧ y.2 = t.2 := by
              simpa only [Prod.mk.injEq] using hcols
            exact hp.2
          have hyt' : y = t := Prod.ext hytRow hytCol
          exact Prod.ext hxz' hyt'
        · intro hcols
          apply
            ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.gridVertexPair_ne_reverse_of_rank_lt
              hrankXY hrankZT
          have hxtRow : x.1 = t.1 := hxz.trans hztRow
          have hxt : x = t :=
            Prod.ext hxtRow (congrArg Prod.fst hcols)
          have hyzRow : y.1 = z.1 := hxyRow.symm.trans hxz
          have hyzCol : y.2 = z.2 := by
            have hp :
                x.2 = t.2 ∧ y.2 = z.2 := by
              simpa only [Prod.mk.injEq] using hcols
            exact hp.2
          have hyz : y = z := Prod.ext hyzRow hyzCol
          exact Prod.ext hxt hyz
      · apply Disjoint.mono
          ((D.block x.1).connector_interior_subset_path hxyCols)
          ((D.block z.1).connector_interior_subset_path hztCols)
        simpa [GraphPath.NodeDisjoint] using D.row_nodeDisjoint hxz
    · rw [D.connectorPath_eq_vertical hzt hztRow]
      apply Disjoint.symm
      apply Disjoint.mono_right
        ((D.block x.1).connector_interior_subset_path hxyCols)
      exact D.vertical_interior_disjoint_row _ _ x.1
  · rw [D.connectorPath_eq_vertical hxy hxyRow]
    let hxyData :=
      ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.verticalData_of_row_ne
        hxy hxyRow
    by_cases hztRow : z.1 = t.1
    · rw [D.connectorPath_eq_horizontal hzt hztRow]
      let hztCols :=
        ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.horizontalConsecutive_of_row_eq
          hzt hztRow
      apply Disjoint.mono_right
        ((D.block z.1).connector_interior_subset_path hztCols)
      exact D.vertical_interior_disjoint_row _ _ z.1
    · rw [D.connectorPath_eq_vertical hzt hztRow]
      let hztData :=
        ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.verticalData_of_row_ne
          hzt hztRow
      exact D.vertical_pairwise_interior_disjoint
        hxyData.1 hxyData.2 hztData.1 hztData.2 hpairs
        (ChekuriChuzhoy.AppendixB1.OrderedPathGridGeometry.gridVertexPair_ne_reverse_of_rank_lt
          hrankXY hrankZT)

/-- Batched bridge geometry gives the standard connector certificate. -/
noncomputable def toGridConnectorAssemblyCertificate
    (D : OrderedBridgeGridGeometry G g) :
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

/-- Ordered rows plus batched vertical bridges contain a canonical grid
minor. -/
theorem containsGridMinor
    (D : OrderedBridgeGridGeometry G g) :
    ContainsGridMinor G g :=
  D.toGridConnectorAssemblyCertificate.containsGridMinor

end OrderedBridgeGridGeometry

end Exponent7
end SimpleGraph

end Lax17Proofs
