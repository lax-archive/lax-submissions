import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3AugmentedBoundary
import Lax17Proofs.Source.AppendixA3Lemma75Arithmetic

namespace Lax17Proofs

universe u v w

/-!
# One budget-preserving pruning step in Observation 7.7

This module combines the exact augmented-boundary update with the
denominator-cleared arithmetic of Observation 7.7.  Accumulating the actual
deleted-edge finset across multiple steps is intentionally kept separate.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Retaining `A` from a partition `(A,B)` preserves the source budget whenever
the violating cut has fewer than one ninth as many edges as discarded
augmented-boundary vertices.  The `deleted` argument is the cardinality of the
previously accumulated edge set. -/
theorem pruning_budget_step
    {U A B T : Finset V} {deleted budget : ℕ}
    (hcover : A ∪ B = U) (hdisj : Disjoint A B)
    (hsparse :
      9 * (Section44.edgeBoundary G A B).card ≤
        (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card)
    (hbudget :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G U T).card +
          8 * deleted ≤ budget) :
    (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card +
        8 * (deleted + (Section44.edgeBoundary G A B).card) ≤ budget := by
  classical
  let GammaU :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G U T
  have hAU : A ⊆ U := by
    intro v hv
    rw [← hcover]
    exact Finset.mem_union_left _ hv
  have hBU : B ⊆ U := by
    intro v hv
    rw [← hcover]
    exact Finset.mem_union_right _ hv
  have hUdiffA : U \ A = B := by
    apply Finset.Subset.antisymm
    · intro v hv
      rcases Finset.mem_sdiff.mp hv with ⟨hvU, hvA⟩
      rw [← hcover] at hvU
      rcases Finset.mem_union.mp hvU with hvA' | hvB
      · exact (hvA hvA').elim
      · exact hvB
    · intro v hvB
      exact Finset.mem_sdiff.mpr
        ⟨hBU hvB, fun hvA => Finset.disjoint_left.mp hdisj hvA hvB⟩
  have hGammaU_subset : GammaU ⊆ U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvBoundary | hvTerminal
    · exact
        ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
          hvBoundary).1
    · exact (Finset.mem_inter.mp hvTerminal).2
  have hGammaSplit :
      GammaU.card = (A ∩ GammaU).card + (B ∩ GammaU).card := by
    have hEq : GammaU = (A ∩ GammaU) ∪ (B ∩ GammaU) := by
      apply Finset.Subset.antisymm
      · intro v hvGamma
        have hvU := hGammaU_subset hvGamma
        rw [← hcover] at hvU
        rcases Finset.mem_union.mp hvU with hvA | hvB
        · exact Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨hvA, hvGamma⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hvB, hvGamma⟩)
      · intro v hv
        rcases Finset.mem_union.mp hv with hvA | hvB
        · exact (Finset.mem_inter.mp hvA).2
        · exact (Finset.mem_inter.mp hvB).2
    calc
      GammaU.card = ((A ∩ GammaU) ∪ (B ∩ GammaU)).card :=
        congrArg Finset.card hEq
      _ = (A ∩ GammaU).card + (B ∩ GammaU).card :=
        Finset.card_union_of_disjoint
          (hdisj.mono inter_subset_left inter_subset_left)
  have hnewMass :
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card ≤
        (A ∩ GammaU).card + (Section44.edgeBoundary G A B).card := by
    have h :=
      Lax17Proofs.SimpleGraph.AppendixA3AugmentedBoundary.augmentedBoundaryVertices_card_le_retained_add_cut
        (G := G) (T := T) hAU
    simpa [GammaU, hUdiffA] using h
  apply denominator_cleared_budget_update
    (oldMass := GammaU.card)
    (retained := (A ∩ GammaU).card)
    (discarded := (B ∩ GammaU).card)
    (newMass :=
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card)
    (newCutEndpoints := (Section44.edgeBoundary G A B).card)
    (cutEdges := (Section44.edgeBoundary G A B).card)
    (deleted := deleted) (budget := budget)
  · exact hGammaSplit
  · exact hnewMass
  · exact le_rfl
  · simpa [GammaU] using hsparse
  · simpa [GammaU] using hbudget

end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
