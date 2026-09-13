import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax17Proofs.Source.GridMinor
import Lax17Proofs.Source.PathOfSets

namespace Lax17Proofs

universe u v w

/-!
# Structural vocabulary for Chekuri--Chuzhoy contracts

This file contains only the lightweight definitions needed to state the
structural, non-algorithmic forms of the Chekuri--Chuzhoy results used in the
path-of-sets-to-grid conversion.  The definitions intentionally reuse the
project's `GraphPath`, `PathPacking`, `PerfectPathPacking`, and
`ContainsGridMinor` notions instead of introducing another graph hierarchy.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


/-- A spanning tree of `G` with at least `L` leaves.

The tree is represented as a spanning subgraph on the same vertex type as `G`;
leaves are vertices of degree exactly one in that subgraph. -/
def HasSpanningTreeWithAtLeastLeaves {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (L : ℕ) : Prop :=
  ∃ T : _root_.SimpleGraph V,
    T ≤ G ∧ T.IsTree ∧
      ∃ leaves : Finset V,
        (∀ v : V, v ∈ leaves ↔ DegreeEquals T v 1) ∧ L ≤ leaves.card

/-- A 2-path in `G` containing at least `p` vertices.

This follows Chekuri--Chuzhoy Section 2.6: every vertex of the path has degree
two in the ambient graph `G`. -/
def ContainsTwoPath {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (p : ℕ) : Prop :=
  ∃ P : GraphPath G,
    p ≤ P.vertexSet.card ∧ ∀ v ∈ P.vertexSet, DegreeEquals G v 2

/-- The auxiliary graph `H(L)` associated with an `A`-`B` linkage `L`.

Its vertices are the paths of `L`.  Two linkage paths are adjacent when there is
a bridge path in `G` connecting them and internally avoiding the entire linkage.
The bridge is unoriented, so the definition accepts either orientation. -/
def linkageAuxGraph {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (L : PerfectPathPacking G A B) :
    _root_.SimpleGraph L.Index where
  Adj i j :=
    i ≠ j ∧
      (Nonempty (L.toPathPacking.BridgeBetween i j) ∨
        Nonempty (L.toPathPacking.BridgeBetween j i))
  symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

/-- The number of degree-two vertices in a finite graph. -/
noncomputable def degreeTwoVertexCount {X : Type u} [Fintype X]
    [DecidableEq X] (H : _root_.SimpleGraph X) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : X => DegreeEquals H x 2).card

/-- The number of degree-two vertices in the auxiliary graph `H(L)`. -/
noncomputable def linkageAuxDegreeTwoCount {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (L : PerfectPathPacking G A B) : ℕ :=
  degreeTwoVertexCount (linkageAuxGraph L)

/-- A linkage is good when its auxiliary graph has no 2-path on
`8 * h + 1` or more vertices. -/
def GoodLinkage {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {A B : Finset V}
    (L : PerfectPathPacking G A B) (h : ℕ) : Prop :=
  ¬ ContainsTwoPath (linkageAuxGraph L) (8 * h + 1)

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
