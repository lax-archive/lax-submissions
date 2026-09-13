import Mathlib.Tactic
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Edge-boundary decompositions for Chuzhoy Lemma 2.11

The minimum balanced-cut proof repeatedly repartitions three disjoint regions.
This module records the exact finite edge-set and cardinality identities needed
for those comparisons.
-/

namespace SimpleGraph
namespace AppendixA3EdgeBoundaryDecomposition


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Edge boundary distributes over a union on the left. -/
theorem edgeBoundary_union_left (X Y Z : Finset V) :
    Section44.edgeBoundary G (X ∪ Y) Z =
      Section44.edgeBoundary G X Z ∪ Section44.edgeBoundary G Y Z := by
  classical
  ext e
  constructor
  · intro he
    rcases ((Section44.mem_edgeBoundary (G := G) (X ∪ Y) Z e).1 he) with
      ⟨heG, v, hv, z, hz, rfl⟩
    rcases Finset.mem_union.mp hv with hvX | hvY
    · exact Finset.mem_union_left _
        ((Section44.mem_edgeBoundary (G := G) X Z s(v, z)).2
          ⟨heG, v, hvX, z, hz, rfl⟩)
    · exact Finset.mem_union_right _
        ((Section44.mem_edgeBoundary (G := G) Y Z s(v, z)).2
          ⟨heG, v, hvY, z, hz, rfl⟩)
  · intro he
    rcases Finset.mem_union.mp he with heXZ | heYZ
    · rcases ((Section44.mem_edgeBoundary (G := G) X Z e).1 heXZ) with
        ⟨heG, x, hx, z, hz, rfl⟩
      exact (Section44.mem_edgeBoundary (G := G) (X ∪ Y) Z s(x, z)).2
        ⟨heG, x, Finset.mem_union_left _ hx, z, hz, rfl⟩
    · rcases ((Section44.mem_edgeBoundary (G := G) Y Z e).1 heYZ) with
        ⟨heG, y, hy, z, hz, rfl⟩
      exact (Section44.mem_edgeBoundary (G := G) (X ∪ Y) Z s(y, z)).2
        ⟨heG, y, Finset.mem_union_right _ hy, z, hz, rfl⟩

/-- Boundaries from two disjoint left regions to a third disjoint region are
disjoint edge sets. -/
theorem edgeBoundary_disjoint_of_three_regions
    {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) :
    Disjoint (Section44.edgeBoundary G X Z)
      (Section44.edgeBoundary G Y Z) := by
  classical
  rw [Finset.disjoint_left]
  intro e heXZ heYZ
  rcases ((Section44.mem_edgeBoundary (G := G) X Z e).1 heXZ) with
    ⟨_heG, x, hx, z, hz, rfl⟩
  rcases ((Section44.mem_edgeBoundary (G := G) Y Z s(x, z)).1 heYZ) with
    ⟨_heG', y, hy, z', hz', heq⟩
  rw [Sym2.eq_iff] at heq
  rcases heq with heq | heq
  · exact Finset.disjoint_left.mp hXY hx (by simpa [heq.1] using hy)
  · exact Finset.disjoint_left.mp hXZ hx (by simpa [heq.1] using hz')

/-- Cardinality form of left-union distribution for three disjoint regions. -/
theorem edgeBoundary_union_left_card
    {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) :
    (Section44.edgeBoundary G (X ∪ Y) Z).card =
      (Section44.edgeBoundary G X Z).card +
        (Section44.edgeBoundary G Y Z).card := by
  rw [edgeBoundary_union_left]
  exact Finset.card_union_of_disjoint
    (edgeBoundary_disjoint_of_three_regions (G := G) hXY hXZ)

/-- Cardinality form of distribution over a union on the right. -/
theorem edgeBoundary_union_right_card
    {X Y Z : Finset V}
    (hYZ : Disjoint Y Z) (hXY : Disjoint X Y) :
    (Section44.edgeBoundary G X (Y ∪ Z)).card =
      (Section44.edgeBoundary G X Y).card +
        (Section44.edgeBoundary G X Z).card := by
  rw [Section44.edgeBoundary_comm (G := G) X (Y ∪ Z),
    edgeBoundary_union_left_card (G := G) hYZ hXY.symm,
    Section44.edgeBoundary_comm (G := G) Y X,
    Section44.edgeBoundary_comm (G := G) Z X]

/-- Rotating a cut across three pairwise-disjoint regions replaces exactly the
`X`--`B` edge family by the `X`--`Y` edge family.  This is the additive form
used to contradict minimum balanced-cut cardinality in Lemma 2.11. -/
theorem rotated_cut_card_add_eq
    {X Y B : Finset V}
    (hXY : Disjoint X Y) (hXB : Disjoint X B)
    (hYB : Disjoint Y B) :
    (Section44.edgeBoundary G (B ∪ X) Y).card +
        (Section44.edgeBoundary G X B).card =
      (Section44.edgeBoundary G (X ∪ Y) B).card +
        (Section44.edgeBoundary G X Y).card := by
  have hnew := edgeBoundary_union_left_card (G := G)
    hXB.symm hYB.symm
  have hold := edgeBoundary_union_left_card (G := G) hXY hXB
  rw [Section44.edgeBoundary_comm (G := G) B Y] at hnew
  omega

/-- The symmetric rotation used in the second case of Lemma 2.11. -/
theorem rotated_cut_card_add_eq_symm
    {X Y B : Finset V}
    (hXY : Disjoint X Y) (hXB : Disjoint X B)
    (hYB : Disjoint Y B) :
    (Section44.edgeBoundary G X (B ∪ Y)).card +
        (Section44.edgeBoundary G Y B).card =
      (Section44.edgeBoundary G (X ∪ Y) B).card +
        (Section44.edgeBoundary G X Y).card := by
  rw [Section44.edgeBoundary_comm (G := G) X (B ∪ Y),
    Section44.edgeBoundary_comm (G := G) X Y]
  simpa [Finset.union_comm] using
    (rotated_cut_card_add_eq (G := G) hXY.symm hYB hXB)

end AppendixA3EdgeBoundaryDecomposition
end SimpleGraph

end Lax17Proofs
