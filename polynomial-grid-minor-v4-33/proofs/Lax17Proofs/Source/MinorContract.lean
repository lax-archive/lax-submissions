import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Lax17Proofs.Source.GridContract

namespace Lax17Proofs

universe u v w

/-!
# Graph minor models

This contract file formalizes graph minors by the standard branch-set model.
A minor model of `H` in `G` assigns each vertex of `H` a nonempty connected
branch set in `G`; distinct branch sets are disjoint, and every edge of `H` is
realized by at least one edge of `G` between the corresponding branch sets.
-/

namespace SimpleGraph


/-- A branch-set model witnessing that `H` is a graph minor of `G`. -/
structure MinorModel {W V : Type*}
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) where
  /-- The branch set in `G` assigned to a vertex of `H`. -/
  branchSet : W → Finset V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ w : W, (branchSet w).Nonempty
  /-- Every branch set induces a connected subgraph of `G`. -/
  branch_connected :
    ∀ w : W, (G.induce {v : V | v ∈ branchSet w}).Connected
  /-- Distinct vertices of `H` have disjoint branch sets in `G`. -/
  branch_disjoint :
    ∀ ⦃u v : W⦄, u ≠ v → Disjoint (branchSet u) (branchSet v)
  /-- Every edge of `H` is represented by an edge of `G` between branch sets. -/
  adjacent :
    ∀ ⦃u v : W⦄, H.Adj u v →
      ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

/-- `H` is a graph minor of `G` when there exists a branch-set model of `H` in
`G`. -/
def IsMinor {W V : Type*}
    (H : _root_.SimpleGraph W) (G : _root_.SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)

/-- `G` contains the `(g x g)` grid as a minor.

This is stated using an arbitrary finite graph `H` isomorphic to the canonical
`gridGraph g`, rather than forcing the minor model itself to use the canonical
pair vertex type.
-/
def ContainsGridMinor {V : Type u} (G : _root_.SimpleGraph V) (g : ℕ) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
    (H : _root_.SimpleGraph W),
      IsGridGraph H g ∧ IsMinor H G

end SimpleGraph

end Lax17Proofs
