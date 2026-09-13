import Lax17Proofs.Source.AppendixA3DeletableEdge
import Lax17Proofs.Source.Section46

namespace Lax17Proofs

universe u v w

/-!
# Arithmetic closure for Chuzhoy Claim 7.3

This file formalizes the ratio-cleared terminal-count argument at the end of
Claim 7.3.  It is independent of how the two candidate subsets of the minimum
set are obtained from the bad cut.
-/

namespace SimpleGraph
namespace AppendixA3Claim73


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

private theorem terminal_partition_card
    (S T : Finset V) :
    (S ∩ T).card + (((Finset.univ : Finset V) \ S) ∩ T).card = T.card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext v
    by_cases hvS : v ∈ S <;> simp [hvS]
  · rw [Finset.disjoint_left]
    intro v hvST hvCT
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvCT).1).2
      (Finset.mem_inter.mp hvST).1

/-- A side containing at most half of a scaled well-linked terminal set has
the expected ratio-cleared edge-boundary lower bound. -/
theorem scaled_boundary_lower_of_two_mul_inter_card_le
    {S T : Finset V} {alphaNum alphaDen : ℕ}
    (hwell :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) T alphaNum alphaDen)
    (hsmall : 2 * (S ∩ T).card ≤ T.card) :
    alphaNum * (S ∩ T).card ≤
      alphaDen * (Section44.clusterBoundary G S).card := by
  classical
  have hparts := terminal_partition_card S T
  have hside :
      (S ∩ T).card ≤ (((Finset.univ : Finset V) \ S) ∩ T).card := by
    omega
  have hcut := hwell.2.2.2 S ((Finset.univ : Finset V) \ S)
    (by simp) (by simp) (by simp) (by simp [Finset.disjoint_left])
  rw [Nat.min_eq_left hside] at hcut
  simpa [Section44.clusterBoundary] using hcut

/-- Taking the finite complement does not change the ambient edge boundary. -/
theorem clusterBoundary_complement
    (S : Finset V) :
    Section44.clusterBoundary G ((Finset.univ : Finset V) \ S) =
      Section44.clusterBoundary G S := by
  classical
  unfold Section44.clusterBoundary
  rw [show (Finset.univ : Finset V) \
      ((Finset.univ : Finset V) \ S) = S by simp]
  exact Section44.edgeBoundary_comm
    ((Finset.univ : Finset V) \ S) S

/-- The source's lower bound on the amount of `Gamma` retained by `M`, written
without division:

`alphaNum * |Gamma| <= alphaNum * |M inter Gamma| + alphaDen * gamma`.
-/
theorem gamma_mass_le_of_minimumSetConditions
    {T Gamma M : Finset V} {gamma alphaNum alphaDen : ℕ}
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) Gamma alphaNum alphaDen)
    (hM :
      AppendixA3DeletableEdge.Lemma72SetConditions G T Gamma gamma M) :
    alphaNum * Gamma.card ≤
      alphaNum * (M ∩ Gamma).card + alphaDen * gamma := by
  classical
  let C : Finset V := (Finset.univ : Finset V) \ M
  have hparts := terminal_partition_card M Gamma
  have hpartsC :
      (M ∩ Gamma).card + (C ∩ Gamma).card = Gamma.card := by
    simpa [C] using hparts
  have hCsmall : 2 * (C ∩ Gamma).card ≤ Gamma.card := by
    have hhalf := hM.half_gamma
    omega
  have hCbound :=
    scaled_boundary_lower_of_two_mul_inter_card_le hGamma hCsmall
  have hboundaryEq :
      Section44.clusterBoundary G C = Section44.clusterBoundary G M := by
    simpa [C] using clusterBoundary_complement (G := G) M
  have hCgamma :
      alphaNum * (C ∩ Gamma).card ≤ alphaDen * gamma :=
    hCbound.trans (by
      rw [hboundaryEq]
      exact Nat.mul_le_mul_left alphaDen hM.boundary_card_le)
  calc
    alphaNum * Gamma.card =
        alphaNum * ((M ∩ Gamma).card + (C ∩ Gamma).card) := by
      congr 1
      exact hpartsC.symm
    _ = alphaNum * (M ∩ Gamma).card +
        alphaNum * (C ∩ Gamma).card := Nat.mul_add _ _ _
    _ ≤ alphaNum * (M ∩ Gamma).card + alphaDen * gamma :=
      Nat.add_le_add_left hCgamma _

private theorem inter_card_add_inter_card_eq
    {Z Z' M Gamma : Finset V}
    (hcover : Z ∪ Z' = M) (hdisjoint : Disjoint Z Z') :
    (Z ∩ Gamma).card + (Z' ∩ Gamma).card = (M ∩ Gamma).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_inter.mp hv with ⟨hvZ, hvGamma⟩
        exact Finset.mem_inter.mpr
          ⟨by rw [← hcover]; exact Finset.mem_union_left _ hvZ, hvGamma⟩
      · rcases Finset.mem_inter.mp hv with ⟨hvZ', hvGamma⟩
        exact Finset.mem_inter.mpr
          ⟨by rw [← hcover]; exact Finset.mem_union_right _ hvZ', hvGamma⟩
    · intro hv
      have hvM := (Finset.mem_inter.mp hv).1
      rw [← hcover] at hvM
      rcases Finset.mem_union.mp hvM with hvZ | hvZ'
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hvZ, (Finset.mem_inter.mp hv).2⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hvZ', (Finset.mem_inter.mp hv).2⟩)
  · exact hdisjoint.mono Finset.inter_subset_left Finset.inter_subset_left

/-- Ratio-cleared final contradiction in Claim 7.3.

The bad cut splits the minimum set `M` into `Z` and `Z'`.  Minimality says
that neither part contains half of `Gamma`; cut submodularity says both parts
have boundary at most `gamma`.  Scaled well-linkedness of `Gamma` then forces
`alphaNum * |Gamma| <= 3 * alphaDen * gamma`, contradicting the Menger-cut
threshold. -/
theorem claim_7_3_gamma_arithmetic_false
    {T Gamma M Z Z' : Finset V} {gamma alphaNum alphaDen : ℕ}
    (hGamma :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) Gamma alphaNum alphaDen)
    (hM :
      AppendixA3DeletableEdge.Lemma72SetConditions G T Gamma gamma M)
    (hcover : Z ∪ Z' = M) (hdisjoint : Disjoint Z Z')
    (hZsmall : 2 * (Z ∩ Gamma).card < Gamma.card)
    (hZ'small : 2 * (Z' ∩ Gamma).card < Gamma.card)
    (hZboundary : (Section44.clusterBoundary G Z).card ≤ gamma)
    (hZ'boundary : (Section44.clusterBoundary G Z').card ≤ gamma)
    (hthreshold : 3 * alphaDen * gamma < alphaNum * Gamma.card) :
    False := by
  classical
  have hmass := gamma_mass_le_of_minimumSetConditions hGamma hM
  have hsplit := inter_card_add_inter_card_eq
    (Gamma := Gamma) hcover hdisjoint
  have hZlinked :=
    scaled_boundary_lower_of_two_mul_inter_card_le hGamma
      (Nat.le_of_lt hZsmall)
  have hZ'linked :=
    scaled_boundary_lower_of_two_mul_inter_card_le hGamma
      (Nat.le_of_lt hZ'small)
  have hZgamma :
      alphaNum * (Z ∩ Gamma).card ≤ alphaDen * gamma :=
    hZlinked.trans (Nat.mul_le_mul_left alphaDen hZboundary)
  have hZ'gamma :
      alphaNum * (Z' ∩ Gamma).card ≤ alphaDen * gamma :=
    hZ'linked.trans (Nat.mul_le_mul_left alphaDen hZ'boundary)
  have hupper : alphaNum * Gamma.card ≤ 3 * alphaDen * gamma := by
    calc
      alphaNum * Gamma.card ≤
          alphaNum * (M ∩ Gamma).card + alphaDen * gamma := hmass
      _ = alphaNum *
            ((Z ∩ Gamma).card + (Z' ∩ Gamma).card) +
              alphaDen * gamma := by rw [hsplit]
      _ = alphaNum * (Z ∩ Gamma).card +
            alphaNum * (Z' ∩ Gamma).card + alphaDen * gamma := by
          rw [Nat.mul_add]
      _ ≤ alphaDen * gamma + alphaDen * gamma + alphaDen * gamma :=
        Nat.add_le_add (Nat.add_le_add hZgamma hZ'gamma) le_rfl
      _ = 3 * alphaDen * gamma := by ring
  exact (Nat.not_lt_of_ge hupper) hthreshold

end AppendixA3Claim73
end SimpleGraph

end Lax17Proofs
