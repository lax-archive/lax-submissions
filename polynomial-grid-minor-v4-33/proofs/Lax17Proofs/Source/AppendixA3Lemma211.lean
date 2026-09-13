import Lax17Proofs.Source.AppendixA3BalancedCut
import Lax17Proofs.Source.AppendixA3EdgeBoundaryDecomposition
import Lax17Proofs.Source.AppendixA3AugmentedBoundary
import Lax17Proofs.Source.AppendixA3Lemma211Arithmetic
import Lax17Proofs.Source.AppendixA3Lemma75Start

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Lemma 2.11

A minimum quarter-balanced edge cut retains a well-linked terminal set after
adding the retained-side endpoints of the cut.  The exact new scaled ratio is
`alphaNum / (2 * alphaDen + alphaNum)`.
-/

namespace SimpleGraph
namespace AppendixA3Lemma211


open Finset

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

private theorem inter_partition_card
    {C P Q T : Finset V}
    (hcover : P ∪ Q = C) (hdisj : Disjoint P Q) :
    (C ∩ T).card = (P ∩ T).card + (Q ∩ T).card := by
  classical
  have hsplit : C ∩ T = (P ∩ T) ∪ (Q ∩ T) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_inter.mp hv with ⟨hvC, hvT⟩
      have hvPQ : v ∈ P ∪ Q := by
        rw [hcover]
        exact hvC
      rcases Finset.mem_union.mp hvPQ with hvP | hvQ
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvP, hvT⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvQ, hvT⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hvP | hvQ
      · rcases Finset.mem_inter.mp hvP with ⟨hvP, hvT⟩
        exact Finset.mem_inter.mpr
          ⟨by rw [← hcover]; exact Finset.mem_union_left _ hvP, hvT⟩
      · rcases Finset.mem_inter.mp hvQ with ⟨hvQ, hvT⟩
        exact Finset.mem_inter.mpr
          ⟨by rw [← hcover]; exact Finset.mem_union_right _ hvQ, hvT⟩
  calc
    (C ∩ T).card = ((P ∩ T) ∪ (Q ∩ T)).card :=
      congrArg Finset.card hsplit
    _ = (P ∩ T).card + (Q ∩ T).card :=
      Finset.card_union_of_disjoint
        (hdisj.mono Finset.inter_subset_left Finset.inter_subset_left)

private theorem sdiff_eq_of_union_eq_of_disjoint
    {C P Q : Finset V}
    (hcover : P ∪ Q = C) (hdisj : Disjoint P Q) :
    C \ P = Q := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hvC, hvP⟩
    have hvPQ : v ∈ P ∪ Q := by
      rw [hcover]
      exact hvC
    rcases Finset.mem_union.mp hvPQ with hvP' | hvQ
    · exact (hvP hvP').elim
    · exact hvQ
  · intro hvQ
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · rw [← hcover]
      exact Finset.mem_union_right _ hvQ
    · intro hvP
      exact Finset.disjoint_left.mp hdisj hvP hvQ

private theorem inter_retained_union_cut_card_le
    [Fintype V] {A B X Gamma : Finset V}
    (hXB : Disjoint X B) :
    (X ∩ ((A ∩ Gamma) ∪
      AppendixA3AugmentedBoundary.leftCutBoundaryVertices G A B)).card ≤
      (X ∩ Gamma).card +
        (Section44.edgeBoundary G X B).card := by
  classical
  have hsubset :
      X ∩ ((A ∩ Gamma) ∪
          AppendixA3AugmentedBoundary.leftCutBoundaryVertices G A B) ⊆
        (X ∩ Gamma) ∪
          AppendixA3AugmentedBoundary.leftCutBoundaryVertices G X B := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvX, hv⟩
    rcases Finset.mem_union.mp hv with hvOld | hvCut
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hvX, (Finset.mem_inter.mp hvOld).2⟩)
    · rcases (AppendixA3AugmentedBoundary.mem_leftCutBoundaryVertices
          (G := G)).1 hvCut with ⟨_hvA, w, hwB, hvw⟩
      exact Finset.mem_union_right _
        ((AppendixA3AugmentedBoundary.mem_leftCutBoundaryVertices
          (G := G)).2 ⟨hvX, w, hwB, hvw⟩)
  calc
    (X ∩ ((A ∩ Gamma) ∪
        AppendixA3AugmentedBoundary.leftCutBoundaryVertices G A B)).card ≤
        ((X ∩ Gamma) ∪
          AppendixA3AugmentedBoundary.leftCutBoundaryVertices G X B).card :=
      Finset.card_le_card hsubset
    _ ≤ (X ∩ Gamma).card +
        (AppendixA3AugmentedBoundary.leftCutBoundaryVertices G X B).card :=
      Finset.card_union_le _ _
    _ ≤ (X ∩ Gamma).card +
        (Section44.edgeBoundary G X B).card := by
      apply Nat.add_le_add_left
      exact
        AppendixA3AugmentedBoundary.leftCutBoundaryVertices_card_le_edgeBoundary_card
          (G := G) hXB

private theorem minimum_external_cut_card_le_internal
    [Fintype V] {S Gamma A X Y : Finset V}
    (hGammaS : Gamma ⊆ S)
    (hcut : AppendixA3BalancedCut.IsMinimumQuarterBalancedEdgeCut
      G S Gamma A)
    (horient : ((S \ A) ∩ Gamma).card ≤ (A ∩ Gamma).card)
    (hXA : X ⊆ A) (hYA : Y ⊆ A)
    (hcover : X ∪ Y = A) (hXY : Disjoint X Y) :
    min (Section44.edgeBoundary G X (S \ A)).card
        (Section44.edgeBoundary G Y (S \ A)).card ≤
      (Section44.edgeBoundary G X Y).card := by
  classical
  let B := S \ A
  have hAS : A ⊆ S := hcut.subset
  have hAB : A ∪ B = S := by
    apply Finset.Subset.antisymm
    · intro v hv
      rcases Finset.mem_union.mp hv with hvA | hvB
      · exact hAS hvA
      · exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).1
    · intro v hvS
      by_cases hvA : v ∈ A
      · exact Finset.mem_union_left _ hvA
      · exact Finset.mem_union_right _
          (by simpa [B] using Finset.mem_sdiff.mpr ⟨hvS, hvA⟩)
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).2 hvA
  have hXB : Disjoint X B := by
    rw [Finset.disjoint_left]
    intro v hvX hvB
    exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).2 (hXA hvX)
  have hYB : Disjoint Y B := by
    rw [Finset.disjoint_left]
    intro v hvY hvB
    exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).2 (hYA hvY)
  have hAterm := inter_partition_card (T := Gamma) hcover hXY
  have hSterm := inter_partition_card (T := Gamma) hAB hABdisj
  rw [Finset.inter_eq_right.mpr hGammaS] at hSterm
  have horientB : (B ∩ Gamma).card ≤ (A ∩ Gamma).card := by
    simpa [B] using horient
  have hGammaLeTwiceA : Gamma.card ≤ 2 * (A ∩ Gamma).card := by
    omega
  by_cases hterminal : (X ∩ Gamma).card ≤ (Y ∩ Gamma).card
  · have hYquarter : Gamma.card ≤ 4 * (Y ∩ Gamma).card := by
      omega
    have hBsubset : B ⊆ S := by
      intro v hvB
      exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).1
    have hBXsubset : B ∪ X ⊆ S :=
      Finset.union_subset hBsubset (hXA.trans hAS)
    have hBXYcover : (B ∪ X) ∪ Y = S := by
      calc
        (B ∪ X) ∪ Y = B ∪ (X ∪ Y) := Finset.union_assoc _ _ _
        _ = B ∪ A := congrArg (fun Z => B ∪ Z) hcover
        _ = A ∪ B := Finset.union_comm _ _
        _ = S := hAB
    have hBXYdisj : Disjoint (B ∪ X) Y := by
      rw [Finset.disjoint_left]
      intro v hvBX hvY
      rcases Finset.mem_union.mp hvBX with hvB | hvX
      · exact Finset.disjoint_left.mp hYB hvY hvB
      · exact Finset.disjoint_left.mp hXY hvX hvY
    have hcomplement : S \ (B ∪ X) = Y :=
      sdiff_eq_of_union_eq_of_disjoint hBXYcover hBXYdisj
    have hBquarter : Gamma.card ≤ 4 * (B ∩ Gamma).card := by
      simpa [B] using hcut.complement_quarter
    have hBinter : B ∩ Gamma ⊆ (B ∪ X) ∩ Gamma := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hv).1,
          (Finset.mem_inter.mp hv).2⟩
    have hbalanced :
        AppendixA3BalancedCut.QuarterBalanced S Gamma (B ∪ X) := by
      refine ⟨hBXsubset, ?_, ?_⟩
      · exact hBquarter.trans
          (Nat.mul_le_mul_left 4 (Finset.card_le_card hBinter))
      · rw [hcomplement]
        exact hYquarter
    have hminimal :
        (Section44.edgeBoundary G (X ∪ Y) B).card ≤
          (Section44.edgeBoundary G (B ∪ X) Y).card := by
      calc
        (Section44.edgeBoundary G (X ∪ Y) B).card =
            (Section44.edgeBoundary G A (S \ A)).card := by
          rw [hcover]
        _ ≤ (Section44.edgeBoundary G (B ∪ X) (S \ (B ∪ X))).card :=
          hcut.cut_card_minimal hbalanced
        _ = (Section44.edgeBoundary G (B ∪ X) Y).card := by
          rw [hcomplement]
    have hrotate :=
      AppendixA3EdgeBoundaryDecomposition.rotated_cut_card_add_eq
        (G := G) hXY hXB hYB
    have hleft :
        (Section44.edgeBoundary G X B).card ≤
          (Section44.edgeBoundary G X Y).card := by
      omega
    exact (Nat.min_le_left _ _).trans (by simpa [B] using hleft)
  · have hXquarter : Gamma.card ≤ 4 * (X ∩ Gamma).card := by
      omega
    have hXBYcover : X ∪ (B ∪ Y) = S := by
      calc
        X ∪ (B ∪ Y) = (X ∪ Y) ∪ B := by ac_rfl
        _ = A ∪ B := congrArg (fun Z => Z ∪ B) hcover
        _ = S := hAB
    have hXBYdisj : Disjoint X (B ∪ Y) := by
      rw [Finset.disjoint_left]
      intro v hvX hvBY
      rcases Finset.mem_union.mp hvBY with hvB | hvY
      · exact Finset.disjoint_left.mp hXB hvX hvB
      · exact Finset.disjoint_left.mp hXY hvX hvY
    have hcomplement : S \ X = B ∪ Y :=
      sdiff_eq_of_union_eq_of_disjoint hXBYcover hXBYdisj
    have hBquarter : Gamma.card ≤ 4 * (B ∩ Gamma).card := by
      simpa [B] using hcut.complement_quarter
    have hBinter : B ∩ Gamma ⊆ (B ∪ Y) ∩ Gamma := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hv).1,
          (Finset.mem_inter.mp hv).2⟩
    have hbalanced : AppendixA3BalancedCut.QuarterBalanced S Gamma X := by
      refine ⟨hXA.trans hAS, hXquarter, ?_⟩
      rw [hcomplement]
      exact hBquarter.trans
        (Nat.mul_le_mul_left 4 (Finset.card_le_card hBinter))
    have hminimal :
        (Section44.edgeBoundary G (X ∪ Y) B).card ≤
          (Section44.edgeBoundary G X (B ∪ Y)).card := by
      calc
        (Section44.edgeBoundary G (X ∪ Y) B).card =
            (Section44.edgeBoundary G A (S \ A)).card := by
          rw [hcover]
        _ ≤ (Section44.edgeBoundary G X (S \ X)).card :=
          hcut.cut_card_minimal hbalanced
        _ = (Section44.edgeBoundary G X (B ∪ Y)).card := by
          rw [hcomplement]
    have hrotate :=
      AppendixA3EdgeBoundaryDecomposition.rotated_cut_card_add_eq_symm
        (G := G) hXY hXB hYB
    have hright :
        (Section44.edgeBoundary G Y B).card ≤
          (Section44.edgeBoundary G X Y).card := by
      omega
    exact (Nat.min_le_right _ _).trans (by simpa [B] using hright)

private theorem oriented_partition_scaled_bound
    [Fintype V] {S Gamma A X Y : Finset V}
    {alphaNum alphaDen : ℕ}
    (hwell : Section46.ScaledEdgeWellLinkedIn
      G S Gamma alphaNum alphaDen)
    (hcut : AppendixA3BalancedCut.IsMinimumQuarterBalancedEdgeCut
      G S Gamma A)
    (hXA : X ⊆ A) (hYA : Y ⊆ A)
    (hcover : X ∪ Y = A) (hXY : Disjoint X Y)
    (hexternal :
      (Section44.edgeBoundary G X (S \ A)).card ≤
        (Section44.edgeBoundary G X Y).card) :
    alphaNum * min
        (X ∩ ((A ∩ Gamma) ∪
          AppendixA3AugmentedBoundary.leftCutBoundaryVertices
            G A (S \ A))).card
        (Y ∩ ((A ∩ Gamma) ∪
          AppendixA3AugmentedBoundary.leftCutBoundaryVertices
            G A (S \ A))).card ≤
      (2 * alphaDen + alphaNum) *
        (Section44.edgeBoundary G X Y).card := by
  classical
  let B := S \ A
  have hAS : A ⊆ S := hcut.subset
  have hGammaS : Gamma ⊆ S := hwell.2.2.1
  have hAB : A ∪ B = S := by
    apply Finset.Subset.antisymm
    · intro v hv
      rcases Finset.mem_union.mp hv with hvA | hvB
      · exact hAS hvA
      · exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).1
    · intro v hvS
      by_cases hvA : v ∈ A
      · exact Finset.mem_union_left _ hvA
      · exact Finset.mem_union_right _
          (by simpa [B] using Finset.mem_sdiff.mpr ⟨hvS, hvA⟩)
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).2 hvA
  have hXB : Disjoint X B := by
    rw [Finset.disjoint_left]
    intro v hvX hvB
    exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).2 (hXA hvX)
  have hYB : Disjoint Y B := by
    rw [Finset.disjoint_left]
    intro v hvY hvB
    exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).2 (hYA hvY)
  have hXrestCover : X ∪ (Y ∪ B) = S := by
    calc
      X ∪ (Y ∪ B) = (X ∪ Y) ∪ B := (Finset.union_assoc _ _ _).symm
      _ = A ∪ B := congrArg (fun Z => Z ∪ B) hcover
      _ = S := hAB
  have hXrestDisj : Disjoint X (Y ∪ B) := by
    rw [Finset.disjoint_left]
    intro v hvX hv
    rcases Finset.mem_union.mp hv with hvY | hvB
    · exact Finset.disjoint_left.mp hXY hvX hvY
    · exact Finset.disjoint_left.mp hXB hvX hvB
  have hYrestCover : Y ∪ (X ∪ B) = S := by
    calc
      Y ∪ (X ∪ B) = (X ∪ Y) ∪ B := by ac_rfl
      _ = A ∪ B := congrArg (fun Z => Z ∪ B) hcover
      _ = S := hAB
  have hYrestDisj : Disjoint Y (X ∪ B) := by
    rw [Finset.disjoint_left]
    intro v hvY hv
    rcases Finset.mem_union.mp hv with hvX | hvB
    · exact Finset.disjoint_left.mp hXY hvX hvY
    · exact Finset.disjoint_left.mp hYB hvY hvB
  have hAterm := inter_partition_card (T := Gamma) hcover hXY
  have hSterm := inter_partition_card (T := Gamma) hAB hABdisj
  rw [Finset.inter_eq_right.mpr hGammaS] at hSterm
  by_cases hhalf : 2 * (X ∩ Gamma).card ≤ Gamma.card
  · have hparts :=
      inter_partition_card (T := Gamma) hXrestCover hXrestDisj
    rw [Finset.inter_eq_right.mpr hGammaS] at hparts
    have hxsmall :
        (X ∩ Gamma).card ≤ ((Y ∪ B) ∩ Gamma).card := by
      omega
    have hold := hwell.2.2.2 X (Y ∪ B)
      (hXA.trans hAS)
      (Finset.union_subset (hYA.trans hAS)
        (by intro v hvB
            exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).1))
      hXrestCover hXrestDisj
    rw [Nat.min_eq_left hxsmall,
      AppendixA3EdgeBoundaryDecomposition.edgeBoundary_union_right_card
        (G := G) hYB hXY] at hold
    have hnew := inter_retained_union_cut_card_le
      (G := G) (A := A) (Gamma := Gamma) hXB
    have hnew' :
        (X ∩ ((A ∩ Gamma) ∪
          AppendixA3AugmentedBoundary.leftCutBoundaryVertices
            G A (S \ A))).card ≤
          (X ∩ Gamma).card +
            (Section44.edgeBoundary G X (S \ A)).card := by
      simpa [B] using hnew
    apply scaled_min_bound_of_left
    exact new_terminal_side_scaled_bound hold hexternal
      (Nat.le_refl _) hnew'
  · have hGammaLt : Gamma.card < 2 * (X ∩ Gamma).card := by
      omega
    have hyx : (Y ∩ Gamma).card < (X ∩ Gamma).card := by
      omega
    have hXcomplement : S \ X = Y ∪ B :=
      sdiff_eq_of_union_eq_of_disjoint hXrestCover hXrestDisj
    have hBquarter : Gamma.card ≤ 4 * (B ∩ Gamma).card := by
      simpa [B] using hcut.complement_quarter
    have hBinter : B ∩ Gamma ⊆ (Y ∪ B) ∩ Gamma := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hv).1,
          (Finset.mem_inter.mp hv).2⟩
    have hbalanced : AppendixA3BalancedCut.QuarterBalanced S Gamma X := by
      refine ⟨hXA.trans hAS, ?_, ?_⟩
      · omega
      · rw [hXcomplement]
        exact hBquarter.trans
          (Nat.mul_le_mul_left 4 (Finset.card_le_card hBinter))
    have hminimal :
        (Section44.edgeBoundary G (X ∪ Y) B).card ≤
          (Section44.edgeBoundary G X (B ∪ Y)).card := by
      calc
        (Section44.edgeBoundary G (X ∪ Y) B).card =
            (Section44.edgeBoundary G A (S \ A)).card := by
          rw [hcover]
        _ ≤ (Section44.edgeBoundary G X (S \ X)).card :=
          hcut.cut_card_minimal hbalanced
        _ = (Section44.edgeBoundary G X (B ∪ Y)).card := by
          rw [hXcomplement, Finset.union_comm]
    have hrotate :=
      AppendixA3EdgeBoundaryDecomposition.rotated_cut_card_add_eq_symm
        (G := G) hXY hXB hYB
    have hYexternal :
        (Section44.edgeBoundary G Y B).card ≤
          (Section44.edgeBoundary G X Y).card := by
      omega
    have hXinter : X ∩ Gamma ⊆ (X ∪ B) ∩ Gamma := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hv).1,
          (Finset.mem_inter.mp hv).2⟩
    have hysmall :
        (Y ∩ Gamma).card ≤ ((X ∪ B) ∩ Gamma).card :=
      (Nat.le_of_lt hyx).trans (Finset.card_le_card hXinter)
    have hold := hwell.2.2.2 Y (X ∪ B)
      (hYA.trans hAS)
      (Finset.union_subset (hXA.trans hAS)
        (by intro v hvB
            exact (Finset.mem_sdiff.mp (by simpa [B] using hvB)).1))
      hYrestCover hYrestDisj
    rw [Nat.min_eq_left hysmall,
      AppendixA3EdgeBoundaryDecomposition.edgeBoundary_union_right_card
        (G := G) hXB hXY.symm,
      Section44.edgeBoundary_comm (G := G) Y X] at hold
    have hnew := inter_retained_union_cut_card_le
      (G := G) (A := A) (Gamma := Gamma) hYB
    have hnew' :
        (Y ∩ ((A ∩ Gamma) ∪
          AppendixA3AugmentedBoundary.leftCutBoundaryVertices
            G A (S \ A))).card ≤
          (Y ∩ Gamma).card +
            (Section44.edgeBoundary G Y (S \ A)).card := by
      simpa [B] using hnew
    apply scaled_min_bound_of_right
    exact new_terminal_side_scaled_bound hold
      (by simpa [B] using hYexternal) (Nat.le_refl _) hnew'

/-- Chuzhoy Lemma 2.11 in the one-sided retained-cut interface. -/
theorem minimumQuarterBalancedEdgeCut_retained_wellLinked
    [Fintype V] {S Gamma A : Finset V} {alphaNum alphaDen : ℕ}
    (hwell : Section46.ScaledEdgeWellLinkedIn
      G S Gamma alphaNum alphaDen)
    (hcut : AppendixA3BalancedCut.IsMinimumQuarterBalancedEdgeCut
      G S Gamma A)
    (horient : ((S \ A) ∩ Gamma).card ≤ (A ∩ Gamma).card) :
    Section46.ScaledEdgeWellLinkedIn G A
      ((A ∩ Gamma) ∪
        AppendixA3AugmentedBoundary.leftCutBoundaryVertices
          G A (S \ A))
      alphaNum (2 * alphaDen + alphaNum) := by
  classical
  refine ⟨hwell.1, ?_, ?_, ?_⟩
  · omega
  · intro v hv
    rcases Finset.mem_union.mp hv with hvOld | hvCut
    · exact (Finset.mem_inter.mp hvOld).1
    · exact
        ((AppendixA3AugmentedBoundary.mem_leftCutBoundaryVertices
          (G := G)).1 hvCut).1
  · intro X Y hXA hYA hcover hXY
    have hobservation := minimum_external_cut_card_le_internal
      (G := G) hwell.2.2.1 hcut horient hXA hYA hcover hXY
    by_cases hleft :
        (Section44.edgeBoundary G X (S \ A)).card ≤
          (Section44.edgeBoundary G Y (S \ A)).card
    · have hXexternal :
          (Section44.edgeBoundary G X (S \ A)).card ≤
            (Section44.edgeBoundary G X Y).card := by
        rw [Nat.min_eq_left hleft] at hobservation
        exact hobservation
      exact oriented_partition_scaled_bound hwell hcut hXA hYA
        hcover hXY hXexternal
    · have hright :
          (Section44.edgeBoundary G Y (S \ A)).card ≤
            (Section44.edgeBoundary G X (S \ A)).card := by
        omega
      have hYexternal :
          (Section44.edgeBoundary G Y (S \ A)).card ≤
            (Section44.edgeBoundary G X Y).card := by
        rw [Nat.min_eq_right hright] at hobservation
        exact hobservation
      have hYexternal' :
          (Section44.edgeBoundary G Y (S \ A)).card ≤
            (Section44.edgeBoundary G Y X).card := by
        rw [Section44.edgeBoundary_comm (G := G) Y X]
        exact hYexternal
      have hswapped := oriented_partition_scaled_bound hwell hcut hYA hXA
        (by simpa only [Finset.union_comm] using hcover) hXY.symm hYexternal'
      simpa only [Nat.min_comm,
        Section44.edgeBoundary_comm (G := G) Y X] using hswapped

/-- Lemma 2.11 specialized to the augmented boundary of a retained set. -/
theorem minimumQuarterBalancedEdgeCut_augmentedBoundary_wellLinked
    [Fintype V] {S T A : Finset V} {alphaNum alphaDen : ℕ}
    (hwell : Section46.ScaledEdgeWellLinkedIn G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T)
      alphaNum alphaDen)
    (hcut : AppendixA3BalancedCut.IsMinimumQuarterBalancedEdgeCut G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) A)
    (horient :
      ((S \ A) ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card) :
    Section46.ScaledEdgeWellLinkedIn G A
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T)
      alphaNum (2 * alphaDen + alphaNum) := by
  rw [AppendixA3AugmentedBoundary.augmentedBoundaryVertices_eq_retained_union_cut
    (G := G) hcut.subset]
  exact minimumQuarterBalancedEdgeCut_retained_wellLinked hwell hcut horient

/-- The source-facing `alphaNum / (3 * alphaDen)` consequence of Lemma 2.11. -/
theorem minimumQuarterBalancedEdgeCut_augmentedBoundary_wellLinked_three
    [Fintype V] {S T A : Finset V} {alphaNum alphaDen : ℕ}
    (hwell : Section46.ScaledEdgeWellLinkedIn G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T)
      alphaNum alphaDen)
    (hcut : AppendixA3BalancedCut.IsMinimumQuarterBalancedEdgeCut G S
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G S T) A)
    (horient :
      ((S \ A) ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card ≤
        (A ∩ AppendixA3ClusterSplit.augmentedBoundaryVertices G S T).card) :
    Section46.ScaledEdgeWellLinkedIn G A
      (AppendixA3ClusterSplit.augmentedBoundaryVertices G A T)
      alphaNum (3 * alphaDen) := by
  exact AppendixA3Lemma75.scaledEdgeWellLinkedIn_weaken_two_add_to_three
    (minimumQuarterBalancedEdgeCut_augmentedBoundary_wellLinked
      hwell hcut horient) hwell.2.1

end AppendixA3Lemma211
end SimpleGraph

end Lax17Proofs
