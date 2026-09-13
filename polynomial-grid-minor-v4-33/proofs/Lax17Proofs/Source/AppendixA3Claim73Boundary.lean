import Lax17Proofs.Source.AppendixA3Claim73Arithmetic
import Lax17Proofs.Source.AppendixA3CutSubmodularity

namespace Lax17Proofs

universe u v w

/-!
# Boundary estimates for Chuzhoy Claim 7.3

This file combines the two cut inequalities with the bad-cut upper bound and
terminal well-linkedness.  It proves that the two pieces of the minimum set
both retain boundary at most `gamma`.
-/

namespace SimpleGraph
namespace AppendixA3Claim73


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

private theorem part_le_of_scaled_cut_bounds
    {alphaNum alphaDen terminalMass cutSize minimumSize outerSize partSize gamma : ℕ}
    (hsub : outerSize + partSize ≤ cutSize + minimumSize)
    (hbad : alphaDen * cutSize < alphaNum * terminalMass + alphaDen)
    (hlower : alphaNum * terminalMass ≤ alphaDen * outerSize)
    (hminimum : minimumSize ≤ gamma) :
    partSize ≤ gamma := by
  have hsubScaled := Nat.mul_le_mul_left alphaDen hsub
  rw [Nat.mul_add, Nat.mul_add] at hsubScaled
  have hminimumScaled := Nat.mul_le_mul_left alphaDen hminimum
  have htotal :
      alphaDen * partSize + alphaDen * outerSize <
        alphaDen * outerSize + alphaDen + alphaDen * gamma := by
    calc
      alphaDen * partSize + alphaDen * outerSize =
          alphaDen * outerSize + alphaDen * partSize := by omega
      _ ≤ alphaDen * cutSize + alphaDen * minimumSize := hsubScaled
      _ < (alphaNum * terminalMass + alphaDen) +
          alphaDen * minimumSize :=
        Nat.add_lt_add_right hbad _
      _ ≤ (alphaNum * terminalMass + alphaDen) +
          alphaDen * gamma :=
        Nat.add_le_add_left hminimumScaled _
      _ ≤ (alphaDen * outerSize + alphaDen) +
          alphaDen * gamma :=
        Nat.add_le_add_right (Nat.add_le_add_right hlower alphaDen)
          (alphaDen * gamma)
      _ = alphaDen * outerSize + alphaDen + alphaDen * gamma := by omega
  have hpartScaled :
      alphaDen * partSize < alphaDen * (gamma + 1) := by
    rw [Nat.mul_add]
    omega
  have hpart : partSize < gamma + 1 :=
    Nat.lt_of_mul_lt_mul_left hpartScaled
  omega

private theorem union_inter_terminals_of_disjoint
    {A M T : Finset V} (hMT : Disjoint M T) :
    (A ∪ M) ∩ T = A ∩ T := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvAM, hvT⟩
    rcases Finset.mem_union.mp hvAM with hvA | hvM
    · exact Finset.mem_inter.mpr ⟨hvA, hvT⟩
    · exact False.elim (Finset.disjoint_left.mp hMT hvM hvT)
  · intro hv
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hv).1,
        (Finset.mem_inter.mp hv).2⟩

private theorem sdiff_inter_terminals_of_disjoint
    {A M T : Finset V} (hMT : Disjoint M T) :
    (A \ M) ∩ T = A ∩ T := by
  ext v
  constructor
  · intro hv
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).1).1,
        (Finset.mem_inter.mp hv).2⟩
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvA, hvT⟩
    have hvM : v ∉ M := by
      intro hvM
      exact Finset.disjoint_left.mp hMT hvM hvT
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hvA, hvM⟩, hvT⟩

/-- The boundary conclusion obtained from the two submodularity inequalities
in Claim 7.3.

The hypothesis `hbad` is the ratio-cleared output of the deleted-edge bad-cut
certificate.  The side `A` is oriented to contain at most half of `T`.
-/
theorem cut_parts_boundary_le_gamma
    {T A M : Finset V} {gamma alphaNum alphaDen : ℕ}
    (hTwell :
      Section46.ScaledEdgeWellLinkedIn
        G (Finset.univ : Finset V) T alphaNum alphaDen)
    (hMT : Disjoint M T)
    (hsmall : 2 * (A ∩ T).card ≤ T.card)
    (hbad :
      alphaDen * (Section44.clusterBoundary G A).card <
        alphaNum * (A ∩ T).card + alphaDen)
    (hMboundary : (Section44.clusterBoundary G M).card ≤ gamma) :
    (Section44.clusterBoundary G (A ∩ M)).card ≤ gamma ∧
      (Section44.clusterBoundary G (M \ A)).card ≤ gamma := by
  classical
  have hUnionTerminals := union_inter_terminals_of_disjoint
    (A := A) (M := M) (T := T) hMT
  have hDiffTerminals := sdiff_inter_terminals_of_disjoint
    (A := A) (M := M) (T := T) hMT
  have hUnionSmall : 2 * ((A ∪ M) ∩ T).card ≤ T.card := by
    simpa [hUnionTerminals] using hsmall
  have hDiffSmall : 2 * ((A \ M) ∩ T).card ≤ T.card := by
    simpa [hDiffTerminals] using hsmall
  have hUnionLower :=
    scaled_boundary_lower_of_two_mul_inter_card_le hTwell hUnionSmall
  have hDiffLower :=
    scaled_boundary_lower_of_two_mul_inter_card_le hTwell hDiffSmall
  rw [hUnionTerminals] at hUnionLower
  rw [hDiffTerminals] at hDiffLower
  constructor
  · exact part_le_of_scaled_cut_bounds
      (Section44.clusterBoundary_union_add_inter_card_le G A M)
      hbad hUnionLower hMboundary
  · exact part_le_of_scaled_cut_bounds
      (Section44.clusterBoundary_sdiff_add_sdiff_card_le G A M)
      hbad hDiffLower hMboundary

end AppendixA3Claim73
end SimpleGraph

end Lax17Proofs
