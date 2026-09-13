import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Edge-Menger definitions

This file contains the statement-level vocabulary for the finite edge-Menger
theorem used in Chuzhoy--Tan Section 4.4.  The theorem is stated for paths
that stay inside a finite cluster `C`: if there are not `k` edge-disjoint
`A`--`B` paths in `C`, then a cut of size `< k` separates `A` from `B` inside
`C`.
-/

namespace SimpleGraph
namespace EdgeMenger


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Restrict an edge-disjoint path packing to a finite set of indices. -/
noncomputable def restrictEdgePathPacking
    {S T : Finset V} (P : EdgePathPacking G S T) (I : Finset P.Index) :
    EdgePathPacking G S T where
  Index := {i : P.Index // i ∈ I}
  path := fun i => P.path i.1
  connects := fun i => P.connects i.1
  edge_disjoint := by
    intro i j hij
    exact P.edge_disjoint (fun h => hij (Subtype.ext h))

@[simp] theorem restrictEdgePathPacking_card
    {S T : Finset V} (P : EdgePathPacking G S T) (I : Finset P.Index) :
    (restrictEdgePathPacking P I).card = I.card := by
  classical
  simp [restrictEdgePathPacking, EdgePathPacking.card]

theorem restrictEdgePathPacking_staysIn
    {S T U : Finset V} {P : EdgePathPacking G S T} {I : Finset P.Index}
    (hP : P.StaysIn U) :
    (restrictEdgePathPacking P I).StaysIn U := by
  intro i
  exact hP i.1

/-- The finite edge boundary between two vertex sets. -/
noncomputable def edgeBoundary [Fintype V]
    (G : _root_.SimpleGraph V) (X Y : Finset V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e : Sym2 V =>
    e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y)

theorem mem_edgeBoundary [Fintype V]
    (X Y : Finset V) (e : Sym2 V) :
    e ∈ edgeBoundary G X Y ↔
      e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y) := by
  classical
  simp [edgeBoundary]

/-- A finite family of `k` edge-disjoint `A`--`B` paths contained in `C`. -/
def HasEdgeDisjointPathsIn
    (G : _root_.SimpleGraph V) (C A B : Finset V) (k : ℕ) : Prop :=
  ∃ P : EdgePathPacking G A B, k ≤ P.card ∧ P.StaysIn C

theorem exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn
    {C A B : Finset V} {k : ℕ}
    (h : HasEdgeDisjointPathsIn G C A B k) :
    ∃ P : EdgePathPacking G A B, P.card = k ∧ P.StaysIn C := by
  classical
  rcases h with ⟨P, hk, hstay⟩
  rcases Finset.exists_subset_card_eq hk with ⟨I, _hsub, hIcard⟩
  refine ⟨restrictEdgePathPacking P I, ?_, ?_⟩
  · simp [hIcard]
  · exact restrictEdgePathPacking_staysIn hstay

/-- A set of edges separates `A` from `B` for paths contained in `C` when every
`A`--`B` path whose vertices stay in `C` uses one of these edges. -/
def EdgeSeparatorIn
    (G : _root_.SimpleGraph V) (C A B : Finset V)
    (F : Finset (Sym2 V)) : Prop :=
  ∀ P : GraphPath G, P.Connects A B → P.vertexSet ⊆ C →
    ∃ e ∈ P.edgeSet, e ∈ F

/-- The cut form of edge-Menger used by Section 4.4.  The partition is of the
cluster vertex set `C`, puts `A` on the left and `B` on the right, and its
boundary has size `< k`. -/
structure CutPartition [Fintype V]
    (G : _root_.SimpleGraph V) (C A B : Finset V) (k : ℕ) where
  /-- Left side of the cut. -/
  X : Finset V
  /-- Right side of the cut. -/
  Y : Finset V
  /-- The cut covers the cluster. -/
  cover : X ∪ Y = C
  /-- The cut sides are disjoint. -/
  disjoint : Disjoint X Y
  /-- Left terminals are on the left. -/
  left_subset : A ⊆ X
  /-- Right terminals are on the right. -/
  right_subset : B ⊆ Y
  /-- The edge boundary is smaller than the target packing size. -/
  boundary_lt : (edgeBoundary G X Y).card < k

/-- The contract-shaped finite edge-Menger cut statement. -/
def EdgeMengerCutStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (C A B : Finset V) (k : ℕ),
      A ⊆ C →
        B ⊆ C →
          Disjoint A B →
            ¬ HasEdgeDisjointPathsIn G C A B k →
              Nonempty (CutPartition G C A B k)

end EdgeMenger
end SimpleGraph

end Lax17Proofs
