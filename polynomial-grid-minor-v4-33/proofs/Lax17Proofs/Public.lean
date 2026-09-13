import Lax17.PolynomialGridMinor
import Lax17Proofs.Source.PolynomialGridMinorComplete

namespace Lax17Proofs

universe u v

namespace Bridge

/-- Repackage a public tree decomposition for the internal proof API. -/
def treeDecompositionToSource {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (D : Lax17.Treewidth.TreeDecomposition G) :
    Lax17Proofs.SimpleGraph.TreeDecomposition G where
  Node := D.Node
  nodeFintype := D.nodeFintype
  nodeDecidableEq := D.nodeDecidableEq
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  vertex_mem_bag := D.vertex_mem_bag
  edge_mem_bag := D.edge_mem_bag
  bag_indices_connected := D.bag_indices_connected

/-- Repackage an internal tree decomposition for the public API. -/
def treeDecompositionToPublic {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (D : Lax17Proofs.SimpleGraph.TreeDecomposition G) :
    Lax17.Treewidth.TreeDecomposition G where
  Node := D.Node
  nodeFintype := D.nodeFintype
  nodeDecidableEq := D.nodeDecidableEq
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  vertex_mem_bag := D.vertex_mem_bag
  edge_mem_bag := D.edge_mem_bag
  bag_indices_connected := D.bag_indices_connected

@[simp] theorem treeDecompositionToSource_width
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (D : Lax17.Treewidth.TreeDecomposition G) :
    (treeDecompositionToSource D).width = D.width :=
  rfl

@[simp] theorem treeDecompositionToPublic_width
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (D : Lax17Proofs.SimpleGraph.TreeDecomposition G) :
    (treeDecompositionToPublic D).width = D.width :=
  rfl

theorem hasTreewidthAtMost_iff {V : Type u}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    Lax17Proofs.SimpleGraph.HasTreewidthAtMost G k ↔
      Lax17.Treewidth.HasTreewidthAtMost G k := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨treeDecompositionToPublic D, by simpa using hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨treeDecompositionToSource D, by simpa using hD⟩

private theorem publicTreewidth_le_of_hasTreewidthAtMost
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ}
    (h : Lax17.Treewidth.HasTreewidthAtMost G k) :
    Lax17.Treewidth.treewidth G ≤ k := by
  classical
  have hex : ∃ e, Lax17.Treewidth.HasTreewidthAtMost G e := ⟨k, h⟩
  simp only [Lax17.Treewidth.treewidth, dif_pos hex]
  exact Nat.find_min' hex h

private theorem publicHasTreewidthAtMost_treewidth
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Lax17.Treewidth.HasTreewidthAtMost G
      (Lax17.Treewidth.treewidth G) := by
  classical
  have hex : ∃ k, Lax17.Treewidth.HasTreewidthAtMost G k := by
    rcases Lax17Proofs.SimpleGraph.exists_hasTreewidthAtMost G with
      ⟨k, hk⟩
    exact ⟨k, (hasTreewidthAtMost_iff G k).mp hk⟩
  simpa only [Lax17.Treewidth.treewidth, dif_pos hex] using
    Nat.find_spec hex

/-- The two structurally identical presentations compute the same minimum
decomposition width. -/
theorem treewidth_eq {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Lax17Proofs.SimpleGraph.treewidth G =
      Lax17.Treewidth.treewidth G := by
  apply Nat.le_antisymm
  · apply Lax17Proofs.SimpleGraph.treewidth_le_of_hasTreewidthAtMost
    exact (hasTreewidthAtMost_iff G _).mpr
      (publicHasTreewidthAtMost_treewidth G)
  · apply publicTreewidth_le_of_hasTreewidthAtMost
    exact (hasTreewidthAtMost_iff G _).mp
      (Lax17Proofs.SimpleGraph.hasTreewidthAtMost_treewidth G)

/-- A finite branch-set model gives the set-valued branch-set model exposed
by the concept package. -/
def minorModelToPublic {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : Lax17Proofs.SimpleGraph.MinorModel H G) :
    Lax17.Minor.Model H G where
  branchSet w := ↑(M.branchSet w)
  branch_nonempty w := by
    rcases M.branch_nonempty w with ⟨x, hx⟩
    exact ⟨x, hx⟩
  branch_connected w := M.branch_connected w
  branch_disjoint := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro z hzx hzy
    exact Finset.disjoint_left.mp (M.branch_disjoint hxy) hzx hzy
  adjacent := M.adjacent

/-- The explicit coordinate grid used internally is the Cartesian product of
two finite path graphs used by the public interface. -/
theorem squareGrid_eq_gridGraph (g : ℕ) :
    Lax17.Grid.squareGrid g =
      Lax17Proofs.SimpleGraph.gridGraph g := by
  ext ⟨r, c⟩ ⟨s, d⟩
  simp [Lax17.Grid.squareGrid, Lax17Proofs.SimpleGraph.gridGraph,
    Lax17Proofs.SimpleGraph.GridAdj,
    Lax17Proofs.SimpleGraph.FinConsecutive,
    _root_.SimpleGraph.pathGraph_adj, and_comm, or_comm]

/-- Convert the implementation's isomorphism-closed finite grid-minor
witness into the canonical public branch-set witness. -/
theorem containsGridMinorToPublic {V : Type u}
    {G : SimpleGraph V} {g : ℕ}
    (h : Lax17Proofs.SimpleGraph.ContainsGridMinor G g) :
    Lax17.GridMinor.ContainsGridMinor G g := by
  rcases h with ⟨W, hWfin, hWdec, H, ⟨e⟩, hminor⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  have hcanonical :
      Lax17Proofs.SimpleGraph.IsMinor
        (Lax17Proofs.SimpleGraph.gridGraph g) G :=
    Lax17Proofs.SimpleGraph.IsMinor.of_iso_left e.symm hminor
  rcases hcanonical with ⟨M⟩
  change Lax17.Minor.IsMinor (Lax17.Grid.squareGrid g) G
  rw [squareGrid_eq_gridGraph]
  exact ⟨minorModelToPublic M⟩

end Bridge

end Lax17Proofs
