import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma211
import Lax17Proofs.Source.AppendixA3Lemma75Arithmetic

namespace Lax17Proofs

universe u v w

/-!
# One main iteration of Chuzhoy Lemma 7.5

This module packages the consequences of retaining the larger side of a
minimum quarter-balanced cut.  Observation 7.7 supplies the one remaining
premise, namely that the cut has at most one eighth as many edges as the old
augmented boundary has vertices.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

private theorem augmentedBoundary_partition_card
    {S T A : Finset V}
    (hGammaS :
      AppendixA3ClusterSplit.augmentedBoundaryVertices G S T ⊆ S) :
    (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card =
      (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card +
        ((S \ A) ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card := by
  classical
  let Gamma := AppendixA3ClusterSplit.augmentedBoundaryVertices G S T
  have hsplit : Gamma = (A ∩ Gamma) ∪ ((S \ A) ∩ Gamma) := by
    apply Finset.Subset.antisymm
    · intro v hvGamma
      by_cases hvA : v ∈ A
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hvA, hvGamma⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨hGammaS hvGamma, hvA⟩, hvGamma⟩)
    · intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
  calc
    Gamma.card = ((A ∩ Gamma) ∪ ((S \ A) ∩ Gamma)).card :=
      congrArg Finset.card hsplit
    _ = (A ∩ Gamma).card + ((S \ A) ∩ Gamma).card :=
      Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_left]
        intro v hvA hvSdiff
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvSdiff).1).2
          (Finset.mem_inter.mp hvA).1)

/-- A retained-side minimum balanced cut supplies a valid next iteration.

The first conclusion is Observation 7.6.  The second is the `7/8`
contraction.  The third says the new augmented boundary retains at least half
of the old one, and the fourth specializes that estimate to the source
threshold `rho`.-/
theorem minimumQuarterBalancedCut_iteration
    {S T A : Finset V} {rho alphaNum alphaDen : ℕ}
    (hwell : Section46.ScaledEdgeWellLinkedIn G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T)
      alphaNum alphaDen)
    (hcut : AppendixA3BalancedCut.IsMinimumQuarterBalancedEdgeCut G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) A)
    (horient :
      ((S \ A) ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card)
    (hcutSmall :
      8 * (Section44.edgeBoundary G A (S \ A)).card ≤
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card)
    (hrho : rho <
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card) :
    Section46.ScaledEdgeWellLinkedIn G A
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T)
        alphaNum (3 * alphaDen) ∧
      8 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card ≤
        7 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ∧
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
        2 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card ∧
      rho ≤
        2 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T).card := by
  classical
  let Gamma := AppendixA3ClusterSplit.augmentedBoundaryVertices G S T
  let GammaA := AppendixA3ClusterSplit.augmentedBoundaryVertices G A T
  have hsplit :
      Gamma.card = (A ∩ Gamma).card + ((S \ A) ∩ Gamma).card := by
    apply augmentedBoundary_partition_card (G := G) hwell.2.2.1
  have horient' :
      ((S \ A) ∩ Gamma).card ≤ (A ∩ Gamma).card := by
    simpa [Gamma] using horient
  have hretainedHalf : Gamma.card ≤ 2 * (A ∩ Gamma).card := by
    omega
  have hretainedThreeQuarter : 4 * (A ∩ Gamma).card ≤ 3 * Gamma.card := by
    have hdiscardedQuarter :
        Gamma.card ≤ 4 * ((S \ A) ∩ Gamma).card := by
      simpa [Gamma] using hcut.complement_quarter
    omega
  have hnewUpper :
      GammaA.card ≤ (A ∩ Gamma).card +
        (Section44.edgeBoundary G A (S \ A)).card := by
    simpa [Gamma, GammaA] using
      Lax17Proofs.SimpleGraph.AppendixA3AugmentedBoundary.augmentedBoundaryVertices_card_le_retained_add_cut
        (G := G) (T := T) hcut.subset
  have hretainedSubset : A ∩ Gamma ⊆ GammaA := by
    simpa [Gamma, GammaA] using
      Lax17Proofs.SimpleGraph.AppendixA3AugmentedBoundary.retained_augmentedBoundaryVertices_subset
        (G := G) (T := T) hcut.subset
  have hretainedCard : (A ∩ Gamma).card ≤ GammaA.card :=
    Finset.card_le_card hretainedSubset
  have hcontract : 8 * GammaA.card ≤ 7 * Gamma.card :=
    eight_mul_newBoundary_le_seven_mul_oldBoundary
      hretainedThreeQuarter (by simpa [Gamma] using hcutSmall) hnewUpper
  have hlower : Gamma.card ≤ 2 * GammaA.card :=
    oldBoundary_le_two_mul_newBoundary hretainedHalf hretainedCard
  refine ⟨?_, hcontract, hlower, ?_⟩
  · exact
      Lax17Proofs.SimpleGraph.AppendixA3Lemma211.minimumQuarterBalancedEdgeCut_augmentedBoundary_wellLinked_three
        hwell hcut horient
  · have hrho' : rho < Gamma.card := by simpa [Gamma] using hrho
    have hthreshold : rho ≤ 2 * GammaA.card := by omega
    simpa [GammaA] using hthreshold

end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
