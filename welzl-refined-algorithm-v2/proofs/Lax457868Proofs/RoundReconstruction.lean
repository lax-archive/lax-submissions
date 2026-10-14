import Mathlib.Tactic
import Lax457868Proofs.ListOrderBounds
import Lax457868Proofs.RefinedContraction
import Lax457868Proofs.GraphTraceBounds
import Lax457868Proofs.TwinExpansion
import Lax457868Proofs.SamplerContract

set_option autoImplicit false

/-!
One explicit reconstruction round: insert each removed ground vertex after
its incidence representative, then derive list and crossing invariants from
the insertion operation.
-/

namespace Lax457868Proofs.RoundReconstruction

open Lax457868Proofs.ContractionRounds
open Lax457868Proofs.GraphTraceBounds
open Lax457868Proofs.RefinedSampleSpec
open Lax457868Proofs.RefinedContraction
open Lax457868Proofs.SamplerContract
open Lax457868Proofs.TwinExpansion
open Lax457868Proofs.ListOrderBounds

noncomputable section

/-- Reconstruct `A` by inserting its removed vertices after their selected
incidence representatives. -/
def reconstructRound {n : ℕ} (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (small : List (Fin n)) : List (Fin n) :=
  insertAllTwins contraction.aChoice.representative small
    ((A \ contraction.retainedA).toList)

lemma removedVertices_nodup {n : ℕ} (G : SimpleGraph (Fin n)) (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W) :
    ((A \ contraction.retainedA).toList).Nodup := by
  exact Finset.nodup_toList _

lemma removedVertices_toFinset {n : ℕ} (G : SimpleGraph (Fin n)) (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W) :
    ((A \ contraction.retainedA).toList).toFinset = A \ contraction.retainedA := by
  simp

lemma removed_representative_mem {n : ℕ} (G : SimpleGraph (Fin n)) (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    {a : Fin n} (ha : a ∈ A) :
    contraction.aChoice.representative a ∈ contraction.retainedA := by
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

lemma reconstructRound_nodup {n : ℕ} (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (small : List (Fin n)) (hsmall : small.Nodup)
    (hsmallSet : small.toFinset = contraction.retainedA) :
    (reconstructRound G A B W contraction small).Nodup := by
  apply nodup_insertAllTwins contraction.aChoice.representative small
    ((A \ contraction.retainedA).toList) hsmall
    (removedVertices_nodup G A B W contraction)
  · intro a ha hmem
    have hdiff := Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)
    have hA : a ∈ A := hdiff.1
    have hR : a ∉ contraction.retainedA := hdiff.2
    have hSfin : a ∈ small.toFinset := List.mem_toFinset.mpr hmem
    have hS : a ∈ contraction.retainedA := hsmallSet ▸ hSfin
    exact hR hS
  · intro a ha
    have hdiff := Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)
    have hA : a ∈ A := hdiff.1
    have hrep := contraction.aChoice.representative_mem a hA
    have hrepR := removed_representative_mem G A B W contraction hdiff.1
    have hrepFin : contraction.aChoice.representative a ∈ small.toFinset :=
      hsmallSet.symm ▸ hrepR
    exact List.mem_toFinset.mp hrepFin

lemma reconstructRound_toFinset {n : ℕ} (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (small : List (Fin n)) (hsmallSet : small.toFinset = contraction.retainedA) :
    (reconstructRound G A B W contraction small).toFinset = A := by
  rw [reconstructRound, toFinset_insertAllTwins]
  · rw [hsmallSet, removedVertices_toFinset G A B W contraction]
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (ha | ⟨ha, _⟩)
      · exact contraction.retainedA_subset ha
      · exact ha
    · intro ha
      by_cases hR : a ∈ contraction.retainedA
      · exact Or.inl hR
      · exact Or.inr ⟨ha, hR⟩
  · intro a ha
    apply List.mem_toFinset.mp
    rw [hsmallSet]
    exact removed_representative_mem G A B W contraction
      (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).1

lemma reconstructRound_subset {n : ℕ} (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (small : List (Fin n)) (hsmallSet : small.toFinset = contraction.retainedA)
    {a : Fin n} (ha : a ∈ reconstructRound G A B W contraction small) :
    a ∈ A := by
  have hfin : a ∈ (reconstructRound G A B W contraction small).toFinset :=
    List.mem_toFinset.mpr ha
  rw [reconstructRound_toFinset G A B W contraction small hsmallSet] at hfin
  exact hfin

lemma restricted_membership_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) {b a : Fin n} (ha : a ∈ A) :
    a ∈ finiteNeighborhood G A b ↔ a ∈ G.neighborSet b := by
  simp [finiteNeighborhood, SimpleGraph.mem_neighborSet, ha]

lemma full_representative_incidence {n : ℕ} (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (a : Fin n) (ha : a ∈ A) (b : Fin n)
    (hb : b ∈ contraction.retainedB) :
    (a ∈ G.neighborSet b ↔
      contraction.aChoice.representative a ∈ G.neighborSet b) := by
  have hrepA := contraction.aChoice.representative_mem a ha
  have hinc := graph_representative_incidence G A B W contraction a ha b hb
  apply (restricted_membership_iff G A ha).symm.trans
  exact hinc.2.trans (restricted_membership_iff G A hrepA)

lemma reconstructRound_preserves_crossing {n : ℕ} (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (small : List (Fin n))
    (b : Fin n) (hb : b ∈ contraction.retainedB) :
    TwinExpansion.crossingCount (contains (G.neighborSet b))
      (reconstructRound G A B W contraction small) =
    TwinExpansion.crossingCount (contains (G.neighborSet b)) small := by
  apply crossingCount_insertAllTwins
  intro a ha
  have haA : a ∈ A := (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).1
  have hinc := full_representative_incidence G A B W contraction a haA b hb
  simp [contains, hinc]

lemma small_subset_A {n : ℕ} (G : SimpleGraph (Fin n))
    (A B W : Finset (Fin n))
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (small : List (Fin n)) (hsmallSet : small.toFinset = contraction.retainedA)
    {a : Fin n} (ha : a ∈ small) : a ∈ A := by
  have hs : a ∈ contraction.retainedA := by
    have hsfin : a ∈ small.toFinset := List.mem_toFinset.mpr ha
    exact hsmallSet ▸ hsfin
  exact contraction.retainedA_subset hs

lemma count_congr_full_restricted {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (l : List (Fin n))
    (hl : ∀ a ∈ l, a ∈ A) (b : Fin n) :
    TwinExpansion.crossingCount (contains (G.neighborSet b)) l =
      TwinExpansion.crossingCount (contains (finiteNeighborhood G A b : Set (Fin n))) l := by
  apply crossingCount_congr_on
  intro a ha
  have haA := hl a ha
  have hmem := restricted_membership_iff G A (b := b) haA
  by_cases h : a ∈ G.neighborSet b <;> simp [contains, hmem, h]

lemma near_twin_restricted_ncard {n c k : ℕ} {G : SimpleGraph (Fin n)}
    (A B W : Finset (Fin n))
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily B
        (finiteNeighborhood G A))
      (A : Set (Fin n)) (W : Set (Fin n))
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (b : Fin n) (hb : b ∈ B) :
    (((finiteNeighborhood G A b : Set (Fin n)) \
        (finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n))) ∪
      ((finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n)) \
        (finiteNeighborhood G A b : Set (Fin n)))).ncard ≤ k := by
  classical
  obtain ⟨_, hnear⟩ := graph_representative_near_twin G A B W hsample contraction b hb
  have hset :
      (((finiteNeighborhood G A b : Set (Fin n)) \
          (finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n))) ∪
        ((finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n)) \
          (finiteNeighborhood G A b : Set (Fin n)))) =
      (↑((finiteNeighborhood G A b \
          finiteNeighborhood G A (contraction.bChoice.representative b)) ∪
        (finiteNeighborhood G A (contraction.bChoice.representative b) \
          finiteNeighborhood G A b)) : Set (Fin n)) := by
    ext a
    simp
  rw [hset, Set.ncard_coe_finset]
  exact hnear

lemma reconstructed_crossing_bound {n c k m : ℕ} {G : SimpleGraph (Fin n)}
    (A B W : Finset (Fin n))
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily B
        (finiteNeighborhood G A))
      (A : Set (Fin n)) (W : Set (Fin n))
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (contraction : TraceContraction A B (finiteNeighborhood G A) W)
    (small : List (Fin n)) (hsmallNodup : small.Nodup)
    (hsmallSet : small.toFinset = contraction.retainedA)
    (hsmallBound : ∀ b ∈ contraction.retainedB,
      TwinExpansion.crossingCount (contains (G.neighborSet b)) small ≤ m) :
    ∀ b ∈ B, TwinExpansion.crossingCount (contains (G.neighborSet b))
      (reconstructRound G A B W contraction small) ≤ m + 2 * k := by
  intro b hb
  classical
  obtain ⟨rbRetained, hnearFin⟩ :=
    graph_representative_near_twin G A B W hsample contraction b hb
  have hsmallRep := hsmallBound (contraction.bChoice.representative b) rbRetained
  have hpres := reconstructRound_preserves_crossing G A B W contraction small
    (contraction.bChoice.representative b) rbRetained
  have hnewRestr := count_congr_full_restricted G A
    (reconstructRound G A B W contraction small)
    (fun a ha => reconstructRound_subset G A B W contraction small hsmallSet ha)
    (contraction.bChoice.representative b)
  have hsameRestr := count_congr_full_restricted G A
    (reconstructRound G A B W contraction small)
    (fun a ha => reconstructRound_subset G A B W contraction small hsmallSet ha) b
  have hpresRestr :
      TwinExpansion.crossingCount
        (contains (finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n)))
        (reconstructRound G A B W contraction small) ≤ m := by
    rw [← hnewRestr, hpres]
    exact hsmallRep
  have hnearSet := near_twin_restricted_ncard (G := G) A B W hsample contraction b hb
  have hstab := crossingCount_le_add_two_mul_symmDiff
    (X := (finiteNeighborhood G A b : Set (Fin n)))
    (Y := (finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n)))
    (l := reconstructRound G A B W contraction small)
    (reconstructRound_nodup G A B W contraction small hsmallNodup hsmallSet)
  have hboundRestr :
      TwinExpansion.crossingCount
        (contains (finiteNeighborhood G A b : Set (Fin n)))
        (reconstructRound G A B W contraction small) ≤ m + 2 * k := by
    calc
      _ ≤ TwinExpansion.crossingCount
            (contains (finiteNeighborhood G A
              (contraction.bChoice.representative b) : Set (Fin n)))
            (reconstructRound G A B W contraction small) +
          2 * (((finiteNeighborhood G A b : Set (Fin n)) \
            (finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n))) ∪
            ((finiteNeighborhood G A (contraction.bChoice.representative b) : Set (Fin n)) \
            (finiteNeighborhood G A b : Set (Fin n)))).ncard := hstab
      _ ≤ m + 2 * k := by omega
  rw [hsameRestr]
  exact hboundRestr

end

end Lax457868Proofs.RoundReconstruction
