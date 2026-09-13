import Mathlib.Tactic
import Lax17Proofs.Source.AppendixA3Lemma78

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Section 7, Observation 7.11

For the degree-three specialization, the lower bound on the augmented
boundary of the hair cluster implies a constant-factor lower bound on its
ordinary boundary.  The proof separates the case in which many original
terminals lie in the hair cluster from the case in which ordinary boundary
vertices account for most of the augmented boundary.
-/

namespace SimpleGraph
namespace AppendixA3Observation711


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

noncomputable section

/-- Observation 7.11, with all ratios cleared and specialized to maximum
degree three.  The source only needs a constant lower bound; `72` is the
explicit constant obtained by the two cases in its proof. -/
theorem rho_le_seventy_two_mul_boundaryVertices_card
    {T X Y : Finset V} {rho kappa : ℕ}
    (hkappa : kappa = 256 * rho)
    (hTcard : T.card = 2 * kappa)
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) T 1 3)
    (hdegree : MaxDegreeAtMost G 3)
    (hXY : Disjoint X Y)
    (hXmass : 3 * kappa ≤ 2 * (X ∩ T).card)
    (hYlarge :
      rho ≤ 4 *
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card) :
    rho ≤ 72 *
      (AppendixA3ClusterSplit.boundaryVertices G Y).card := by
  classical
  let boundary := AppendixA3ClusterSplit.boundaryVertices G Y
  let yterm := T ∩ Y
  have hYtermEq : (Y ∩ T).card = yterm.card := by
    simp [yterm, Finset.inter_comm]
  have hXYterm : Disjoint (X ∩ T) (Y ∩ T) :=
    hXY.mono Finset.inter_subset_left Finset.inter_subset_left
  have hsumXY :
      (X ∩ T).card + (Y ∩ T).card ≤ T.card := by
    rw [← Finset.card_union_of_disjoint hXYterm]
    exact Finset.card_le_card (by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2)
  have hYsmall : 2 * yterm.card ≤ kappa := by
    rw [hYtermEq] at hsumXY
    omega
  have hXoutside :
      X ∩ T ⊆ ((Finset.univ : Finset V) \ Y) ∩ T := by
    intro v hv
    have hvX := (Finset.mem_inter.mp hv).1
    have hvT := (Finset.mem_inter.mp hv).2
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ v,
          fun hvY => Finset.disjoint_left.mp hXY hvX hvY⟩,
        hvT⟩
  have hYleOutside :
      (Y ∩ T).card ≤
        (((Finset.univ : Finset V) \ Y) ∩ T).card := by
    have houtside :
        (X ∩ T).card ≤
          (((Finset.univ : Finset V) \ Y) ∩ T).card :=
      Finset.card_le_card hXoutside
    rw [hYtermEq]
    omega
  by_cases hmuch : rho ≤ 8 * yterm.card
  · have hcover :
        Y ∪ ((Finset.univ : Finset V) \ Y) =
          (Finset.univ : Finset V) := by
      ext v
      simp
    have hdisjoint :
        Disjoint Y ((Finset.univ : Finset V) \ Y) := by
      rw [Finset.disjoint_left]
      intro v hvY hvDiff
      exact (Finset.mem_sdiff.mp hvDiff).2 hvY
    have hcut :=
      hTwell.2.2.2 Y ((Finset.univ : Finset V) \ Y)
        (Finset.subset_univ _) (Finset.subset_univ _) hcover hdisjoint
    rw [Nat.min_eq_left hYleOutside] at hcut
    have hedge :
        yterm.card ≤
          3 * (Section44.clusterBoundary G Y).card := by
      simpa [Section44.clusterBoundary, hYtermEq] using hcut
    have hboundary :
        (Section44.clusterBoundary G Y).card ≤
          3 * boundary.card := by
      simpa [boundary] using
        AppendixA3ClusterSplit.clusterBoundary_card_le_maxDegree_mul_boundaryVertices_card
          (G := G) (S := Y) hdegree
    calc
      rho ≤ 8 * yterm.card := hmuch
      _ ≤ 8 * (3 * (Section44.clusterBoundary G Y).card) :=
        Nat.mul_le_mul_left 8 hedge
      _ ≤ 72 * boundary.card := by
        have := Nat.mul_le_mul_left 24 hboundary
        simpa only [show 8 * (3 *
            (Section44.clusterBoundary G Y).card) =
              24 * (Section44.clusterBoundary G Y).card by ring,
          show 24 * (3 * boundary.card) = 72 * boundary.card by ring]
          using this
  · have hySmall : 8 * yterm.card < rho := Nat.lt_of_not_ge hmuch
    have haug :
        (AppendixA3ClusterSplit.augmentedBoundaryVertices G Y T).card ≤
          boundary.card + yterm.card := by
      simpa [AppendixA3ClusterSplit.augmentedBoundaryVertices,
        boundary, yterm] using
          Finset.card_union_le boundary yterm
    have hrho :
        rho ≤ 4 * (boundary.card + yterm.card) :=
      hYlarge.trans (Nat.mul_le_mul_left 4 haug)
    have hrhoEight : rho ≤ 8 * boundary.card := by omega
    have hEightSeventyTwo :
        8 * boundary.card ≤ 72 * boundary.card :=
      Nat.mul_le_mul_right boundary.card (by decide)
    simpa [boundary] using hrhoEight.trans hEightSeventyTwo

end
end AppendixA3Observation711
end SimpleGraph

end Lax17Proofs
