import Lax17Proofs.Source.Minor
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Path-valued minor certificates

This file packages a common minor-construction pattern used in the grid-minor
proofs: each branch set is the vertex set of a graph path.  Since path vertex
sets induce connected subgraphs, a path-valued certificate immediately gives a
standard branch-set `MinorModel`.
-/

namespace SimpleGraph

/-- A minor certificate whose branch sets are supplied as graph paths.

The certificate still uses the standard branch-set minor convention: each edge
of the pattern graph is witnessed by a host edge between the corresponding path
vertex sets. -/
structure PathMinorModel {W V : Type*} [DecidableEq V]
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) where
  /-- Path-valued branch set for each pattern vertex. -/
  branchPath : W → GraphPath G
  /-- Distinct pattern vertices get disjoint path vertex sets. -/
  branch_disjoint :
    ∀ ⦃x y : W⦄, x ≠ y →
      Disjoint (branchPath x).vertexSet (branchPath y).vertexSet
  /-- Every pattern edge is represented by a host edge between the path branch
  sets. -/
  adjacent :
    ∀ ⦃x y : W⦄, H.Adj x y →
      ∃ u ∈ (branchPath x).vertexSet,
        ∃ v ∈ (branchPath y).vertexSet, G.Adj u v

namespace PathMinorModel

/-- Convert a path-valued minor certificate to the standard branch-set model. -/
noncomputable def toMinorModel {W V : Type*} [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : PathMinorModel H G) : MinorModel H G where
  branchSet := fun x => (M.branchPath x).vertexSet
  branch_nonempty := by
    intro x
    exact ⟨(M.branchPath x).source,
      GraphPath.source_mem_vertexSet (M.branchPath x)⟩
  branch_connected := by
    intro x
    exact GraphPath.connected_induce_vertexSet (M.branchPath x)
  branch_disjoint := M.branch_disjoint
  adjacent := M.adjacent

/-- A path-valued minor certificate proves minor containment. -/
theorem isMinor {W V : Type*} [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
    (M : PathMinorModel H G) : IsMinor H G :=
  ⟨M.toMinorModel⟩

end PathMinorModel

end SimpleGraph

end Lax17Proofs
