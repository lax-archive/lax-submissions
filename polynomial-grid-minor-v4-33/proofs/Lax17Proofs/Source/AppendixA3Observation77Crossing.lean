import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3BalancedCut
import Lax17Proofs.Source.AppendixA3PruningEdges

namespace Lax17Proofs

universe u v w

/-!
# The original-terminal crossing in Observation 7.7

The pruning budget controls the current augmented boundary, but newly created
boundary vertices need not belong to the original augmented boundary.  This
module repairs the crossing argument by tracking the original augmented-
boundary vertices that survive in the current pruning state.

All balance and cut bounds are denominator-cleared natural-number
inequalities.
-/

namespace SimpleGraph
namespace AppendixA3Lemma75


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

private theorem augmentedBoundaryVertices_subset
    {S T : Finset V} :
    AppendixA3ClusterSplit.augmentedBoundaryVertices G S T ⊆ S := by
  intro v hv
  change v ∈ AppendixA3ClusterSplit.boundaryVertices G S ∪ (T ∩ S) at hv
  rcases Finset.mem_union.mp hv with hvBoundary | hvTerminal
  · exact
      ((AppendixA3ClusterSplit.mem_boundaryVertices (G := G)).1
        hvBoundary).1
  · exact (Finset.mem_inter.mp hvTerminal).2

omit [Fintype V] in
private theorem inter_partition_card
    {U A B Gamma : Finset V}
    (hcover : A ∪ B = U) (hdisj : Disjoint A B) :
    (U ∩ Gamma).card =
      (A ∩ Gamma).card + (B ∩ Gamma).card := by
  have hsplit :
      U ∩ Gamma = (A ∩ Gamma) ∪ (B ∩ Gamma) := by
    apply Finset.Subset.antisymm
    · intro v hv
      rcases Finset.mem_inter.mp hv with ⟨hvU, hvGamma⟩
      rw [← hcover] at hvU
      rcases Finset.mem_union.mp hvU with hvA | hvB
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hvA, hvGamma⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hvB, hvGamma⟩)
    · intro v hv
      rcases Finset.mem_union.mp hv with hvA | hvB
      · rcases Finset.mem_inter.mp hvA with ⟨hvA, hvGamma⟩
        have hvU : v ∈ U := by
          rw [← hcover]
          exact Finset.mem_union_left _ hvA
        exact Finset.mem_inter.mpr ⟨hvU, hvGamma⟩
      · rcases Finset.mem_inter.mp hvB with ⟨hvB, hvGamma⟩
        have hvU : v ∈ U := by
          rw [← hcover]
          exact Finset.mem_union_right _ hvB
        exact Finset.mem_inter.mpr ⟨hvU, hvGamma⟩
  calc
    (U ∩ Gamma).card =
        ((A ∩ Gamma) ∪ (B ∩ Gamma)).card := congrArg Finset.card hsplit
    _ = (A ∩ Gamma).card + (B ∩ Gamma).card :=
      Finset.card_union_of_disjoint
        (hdisj.mono inter_subset_left inter_subset_left)

/-- At the first three-quarter crossing of the original augmented-boundary
terminals, the retained side is quarter-balanced in the original set.

The sparse-cut hypothesis is included because this theorem is used at an
actual `retainLeft` step; the balance argument itself only needs the oriented
partition and the predecessor state's budget. -/
theorem quarterBalanced_of_three_quarter_original_crossing
    {S T A B : Finset V} (state : PruningState G S T)
    (hcover : A ∪ B = state.U) (hdisj : Disjoint A B)
    (horient :
      (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card)
    (_hsparse :
      9 * (Section44.edgeBoundary G A B).card <
        (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card)
    (hbefore :
      3 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card <
        4 * (state.U ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card)
    (hafter :
      4 * (A ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
        3 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card) :
    AppendixA3BalancedCut.QuarterBalanced S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) A := by
  classical
  let Omega := AppendixA3ClusterSplit.augmentedBoundaryVertices G S T
  let current :=
    AppendixA3ClusterSplit.augmentedBoundaryVertices G state.U T
  have hAU : A ⊆ state.U := by
    intro v hvA
    rw [← hcover]
    exact Finset.mem_union_left _ hvA
  have hBU : B ⊆ state.U := by
    intro v hvB
    rw [← hcover]
    exact Finset.mem_union_right _ hvB
  have hAS : A ⊆ S := hAU.trans state.U_subset
  have hOmegaS : Omega ⊆ S := by
    simpa [Omega] using
      (augmentedBoundaryVertices_subset (G := G) (S := S) (T := T))
  have hcurrentU : current ⊆ state.U := by
    simpa [current] using
      (augmentedBoundaryVertices_subset
        (G := G) (S := state.U) (T := T))
  have horient' :
      (B ∩ current).card ≤ (A ∩ current).card := by
    simpa [current] using horient
  have hcurrentSplit :
      current.card =
        (A ∩ current).card + (B ∩ current).card := by
    have hsplit := inter_partition_card
      (Gamma := current) hcover hdisj
    rw [Finset.inter_eq_right.mpr hcurrentU] at hsplit
    exact hsplit
  have htwiceBCurrent : 2 * (B ∩ current).card ≤ current.card := by
    omega
  have hcurrentBudget : current.card ≤ Omega.card := by
    have hbudget := state.augmentedBoundary_budget
    change current.card + 8 * state.deletedEdges.card ≤ Omega.card at hbudget
    omega
  have hretainedOriginal : state.U ∩ Omega ⊆ current := by
    simpa [Omega, current] using
      (Lax17Proofs.SimpleGraph.AppendixA3AugmentedBoundary.retained_augmentedBoundaryVertices_subset
          (G := G) (T := T) state.U_subset)
  have hBOriginalCurrent : B ∩ Omega ⊆ B ∩ current := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvB, hvOmega⟩
    exact Finset.mem_inter.mpr
      ⟨hvB, hretainedOriginal (Finset.mem_inter.mpr ⟨hBU hvB, hvOmega⟩)⟩
  have hBOriginalCard :
      (B ∩ Omega).card ≤ (B ∩ current).card :=
    Finset.card_le_card hBOriginalCurrent
  have hOriginalSplit :
      (state.U ∩ Omega).card =
        (A ∩ Omega).card + (B ∩ Omega).card :=
    inter_partition_card (Gamma := Omega) hcover hdisj
  have hkey :
      2 * (state.U ∩ Omega).card ≤
        2 * (A ∩ Omega).card + Omega.card := by
    omega
  have hbefore' :
      3 * Omega.card < 4 * (state.U ∩ Omega).card := by
    simpa [Omega] using hbefore
  have hafter' :
      4 * (A ∩ Omega).card ≤ 3 * Omega.card := by
    simpa [Omega] using hafter
  have hretainedQuarter : Omega.card ≤ 4 * (A ∩ Omega).card := by
    omega
  have hOmegaSplit :
      Omega.card =
        (A ∩ Omega).card + ((S \ A) ∩ Omega).card := by
    have hsplit := inter_partition_card
      (U := S) (A := A) (B := S \ A) (Gamma := Omega)
      (by
        apply Finset.Subset.antisymm
        · exact Finset.union_subset hAS Finset.sdiff_subset
        · intro v hvS
          by_cases hvA : v ∈ A
          · exact Finset.mem_union_left _ hvA
          · exact Finset.mem_union_right _
              (Finset.mem_sdiff.mpr ⟨hvS, hvA⟩))
      (by
        rw [Finset.disjoint_left]
        intro v hvA hvSdiff
        exact (Finset.mem_sdiff.mp hvSdiff).2 hvA)
    rw [Finset.inter_eq_right.mpr hOmegaS] at hsplit
    exact hsplit
  have hcomplementQuarter :
      Omega.card ≤ 4 * ((S \ A) ∩ Omega).card := by
    omega
  exact ⟨hAS, hretainedQuarter, hcomplementQuarter⟩

/-- The crossing step packaged around the actual successor state.  Besides
quarter-balance, its accumulated-edge invariant bounds the external cut by
one eighth of the original augmented-boundary mass. -/
theorem retainLeft_at_three_quarter_original_crossing
    {S T A B : Finset V} (state : PruningState G S T)
    (hcover : A ∪ B = state.U) (hdisj : Disjoint A B)
    (horient :
      (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card)
    (hsparse :
      9 * (Section44.edgeBoundary G A B).card <
        (B ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices
          G state.U T).card)
    (hbefore :
      3 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card <
        4 * (state.U ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card)
    (hafter :
      4 * (A ∩
          AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
        3 * (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card) :
    let next := state.retainLeft hcover hdisj horient hsparse
    AppendixA3BalancedCut.QuarterBalanced S
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) next.U ∧
      8 * (Section44.edgeBoundary G A (S \ A)).card ≤
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card := by
  let next := state.retainLeft hcover hdisj horient hsparse
  change AppendixA3BalancedCut.QuarterBalanced S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) next.U ∧
    8 * (Section44.edgeBoundary G A (S \ A)).card ≤
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card
  have hbalanced := quarterBalanced_of_three_quarter_original_crossing
    state hcover hdisj horient hsparse hbefore hafter
  have hboundary := next.eight_mul_externalBoundary_card_le_initial
  constructor
  · simpa [next, PruningState.retainLeft] using hbalanced
  · simpa [next, PruningState.retainLeft] using hboundary

end AppendixA3Lemma75
end SimpleGraph

end Lax17Proofs
