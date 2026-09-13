import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3ClusterSplit

namespace Lax17Proofs

universe u v w

/-!
# Augmented-boundary bookkeeping for Chuzhoy Section 7

The pruning arguments in Lemmas 7.5 and 7.8 repeatedly replace a current set
`S` by a subset `A`.  This module identifies the resulting augmented boundary
as the old augmented-boundary vertices retained in `A`, together with the
`A`-side endpoints of the cut from `A` to `S \ A`.
-/

namespace SimpleGraph
namespace AppendixA3AugmentedBoundary


open Finset

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- Vertices on the left side of a cut that are incident with a crossing
edge. -/
noncomputable def leftCutBoundaryVertices [Fintype V]
    (G : _root_.SimpleGraph V) (A B : Finset V) : Finset V := by
  classical
  exact A.filter fun v => ∃ w : V, w ∈ B ∧ G.Adj v w

@[simp] theorem mem_leftCutBoundaryVertices [Fintype V]
    {A B : Finset V} {v : V} :
    v ∈ leftCutBoundaryVertices G A B ↔
      v ∈ A ∧ ∃ w : V, w ∈ B ∧ G.Adj v w := by
  classical
  simp [leftCutBoundaryVertices]

/-- Distinct left endpoints choose distinct undirected crossing edges when the
two cut sides are disjoint. -/
theorem leftCutBoundaryVertices_card_le_edgeBoundary_card [Fintype V]
    {A B : Finset V} (hdisj : Disjoint A B) :
    (leftCutBoundaryVertices G A B).card ≤
      (Section44.edgeBoundary G A B).card := by
  classical
  let rightNeighbor :
      {v : V // v ∈ leftCutBoundaryVertices G A B} → V :=
    fun v => Classical.choose
      ((mem_leftCutBoundaryVertices (G := G)).1 v.2).2
  have rightNeighbor_spec
      (v : {v : V // v ∈ leftCutBoundaryVertices G A B}) :
      rightNeighbor v ∈ B ∧ G.Adj v.1 (rightNeighbor v) :=
    Classical.choose_spec
      ((mem_leftCutBoundaryVertices (G := G)).1 v.2).2
  let toBoundaryEdge :
      {v : V // v ∈ leftCutBoundaryVertices G A B} →
        {e : Sym2 V // e ∈ Section44.edgeBoundary G A B} :=
    fun v => ⟨s(v.1, rightNeighbor v), by
      apply (Section44.mem_edgeBoundary (G := G) A B
        s(v.1, rightNeighbor v)).2
      exact ⟨by simpa [_root_.SimpleGraph.mem_edgeSet] using
          (rightNeighbor_spec v).2,
        v.1, ((mem_leftCutBoundaryVertices (G := G)).1 v.2).1,
        rightNeighbor v, (rightNeighbor_spec v).1, rfl⟩⟩
  have hinjective : Function.Injective toBoundaryEdge := by
    intro v w hvw
    apply Subtype.ext
    have hedge := congrArg Subtype.val hvw
    change s(v.1, rightNeighbor v) = s(w.1, rightNeighbor w) at hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with hedge | hedge
    · exact hedge.1
    · exfalso
      have hvA : v.1 ∈ A :=
        ((mem_leftCutBoundaryVertices (G := G)).1 v.2).1
      have hvB : v.1 ∈ B := by
        simpa [hedge.1] using (rightNeighbor_spec w).1
      exact Finset.disjoint_left.mp hdisj hvA hvB
  have hcard := Fintype.card_le_of_injective toBoundaryEdge hinjective
  calc
    (leftCutBoundaryVertices G A B).card =
        Fintype.card {v : V // v ∈ leftCutBoundaryVertices G A B} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
          {e : Sym2 V // e ∈ Section44.edgeBoundary G A B} := hcard
    _ = (Section44.edgeBoundary G A B).card := Fintype.card_coe _

/-- Exact augmented-boundary update after retaining `A ⊆ S`. -/
theorem augmentedBoundaryVertices_eq_retained_union_cut [Fintype V]
    {S A T : Finset V} (hAS : A ⊆ S) :
    AppendixA3ClusterSplit.augmentedBoundaryVertices G A T =
      (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) ∪
        leftCutBoundaryVertices G A (S \ A) := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_union.mp hv with hvBoundary | hvTerminal
    · rcases (AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
          hvBoundary with ⟨hvA, w, hwA, hvw⟩
      by_cases hwS : w ∈ S
      · exact Finset.mem_union_right _
          ((mem_leftCutBoundaryVertices (G := G)).2
            ⟨hvA, w, Finset.mem_sdiff.mpr ⟨hwS, hwA⟩, hvw⟩)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
          ⟨hvA, Finset.mem_union_left _
            ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).2
              ⟨hAS hvA, w, hwS, hvw⟩)⟩)
    · rcases Finset.mem_inter.mp hvTerminal with ⟨hvT, hvA⟩
      exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨hvA, Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hvT, hAS hvA⟩)⟩)
  · intro v hv
    rcases Finset.mem_union.mp hv with hvOld | hvCut
    · rcases Finset.mem_inter.mp hvOld with ⟨hvA, hvAugmented⟩
      rcases Finset.mem_union.mp hvAugmented with hvBoundary | hvTerminal
      · rcases (AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
            hvBoundary with ⟨_hvS, w, hwS, hvw⟩
        exact Finset.mem_union_left _
          ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).2
            ⟨hvA, w, fun hwA => hwS (hAS hwA), hvw⟩)
      · rcases Finset.mem_inter.mp hvTerminal with ⟨hvT, _hvS⟩
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvT, hvA⟩)
    · rcases (mem_leftCutBoundaryVertices (G := G)).1 hvCut with
        ⟨hvA, w, hw, hvw⟩
      exact Finset.mem_union_left _
        ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).2
          ⟨hvA, w, (Finset.mem_sdiff.mp hw).2, hvw⟩)

/-- Cardinal form of the augmented-boundary update.  This is the inequality
used after every retained-side step in Lemmas 7.5 and 7.8. -/
theorem augmentedBoundaryVertices_card_le_retained_add_cut [Fintype V]
    {S A T : Finset V} (hAS : A ⊆ S) :
    (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card ≤
      (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card +
        (Section44.edgeBoundary G A (S \ A)).card := by
  classical
  rw [augmentedBoundaryVertices_eq_retained_union_cut (G := G) hAS]
  calc
    ((A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) ∪
        leftCutBoundaryVertices G A (S \ A)).card ≤
      (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card +
        (leftCutBoundaryVertices G A (S \ A)).card :=
      Finset.card_union_le _ _
    _ ≤ (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card +
        (Section44.edgeBoundary G A (S \ A)).card := by
      apply Nat.add_le_add_left
      apply leftCutBoundaryVertices_card_le_edgeBoundary_card (G := G)
      rw [Finset.disjoint_left]
      intro v hvA hvSdiff
      exact (Finset.mem_sdiff.mp hvSdiff).2 hvA

/-- Every old augmented-boundary vertex retained in `A` remains in the new
augmented boundary. -/
theorem retained_augmentedBoundaryVertices_subset [Fintype V]
    {S A T : Finset V} (hAS : A ⊆ S) :
    A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T ⊆
      AppendixA3ClusterSplit.augmentedBoundaryVertices G A T := by
  rw [augmentedBoundaryVertices_eq_retained_union_cut (G := G) hAS]
  exact Finset.subset_union_left

/-- Projecting the augmented-boundary update to `X ⊆ A`: the terminals seen
in `X` are covered by retained old terminals and the `X`-side endpoints of
the cut from `A` to `S \ A`. -/
theorem inter_augmentedBoundaryVertices_card_le_retained_add_cut [Fintype V]
    {S A X T : Finset V} (hAS : A ⊆ S) (hXA : X ⊆ A) :
    (X ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card ≤
      (X ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card +
        (Section44.edgeBoundary G X (S \ A)).card := by
  classical
  let old := X ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T
  let cut := leftCutBoundaryVertices G X (S \ A)
  have hsubset :
      X ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G A T ⊆
        old ∪ cut := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvX, hvAugmented⟩
    rw [augmentedBoundaryVertices_eq_retained_union_cut (G := G) hAS]
      at hvAugmented
    rcases Finset.mem_union.mp hvAugmented with hvOld | hvCut
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr
          ⟨hvX, (Finset.mem_inter.mp hvOld).2⟩)
    · rcases (mem_leftCutBoundaryVertices (G := G)).1 hvCut with
        ⟨_hvA, w, hw, hvw⟩
      exact Finset.mem_union_right _
        ((mem_leftCutBoundaryVertices (G := G)).2
          ⟨hvX, w, hw, hvw⟩)
  calc
    (X ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card ≤
        (old ∪ cut).card := Finset.card_le_card hsubset
    _ ≤ old.card + cut.card := Finset.card_union_le _ _
    _ ≤ old.card + (Section44.edgeBoundary G X (S \ A)).card := by
      apply Nat.add_le_add_left
      apply leftCutBoundaryVertices_card_le_edgeBoundary_card (G := G)
      rw [Finset.disjoint_left]
      intro v hvX hvSdiff
      exact (Finset.mem_sdiff.mp hvSdiff).2 (hXA hvX)

end AppendixA3AugmentedBoundary
end SimpleGraph

end Lax17Proofs
