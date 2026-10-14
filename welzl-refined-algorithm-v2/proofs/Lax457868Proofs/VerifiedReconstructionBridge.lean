import Lax457868Proofs.RoundReconstruction
import Lax457868Proofs.VerifiedPartitionBridge
import Lax235315Proofs.Construction.ConcreteReconstruction
import Lax235315Proofs.Construction.Reconstruction

/-!
Bridges between the original concrete list reconstruction and the refined
round reconstruction, using the same stored trace-partition representatives.
-/

namespace Lax457868Proofs.VerifiedReconstructionBridge

open scoped symmDiff

open Lax457868Proofs.RefinedSampleSpec
open Lax457868Proofs.VerifiedPartitionBridge
open Lax457868Proofs.RoundReconstruction
open Lax235315Proofs.Construction.ConcreteReconstruction
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.TracePartitions

private lemma insertAfter_eq {α : Type*} [DecidableEq α] (representative new : α)
    (order : List α) :
    Lax235315Proofs.Construction.ListCrossing.insertAfter representative new order =
      Lax457868Proofs.TwinExpansion.insertAfter representative new order := by
  induction order with
  | nil => rfl
  | cons first rest ih =>
      simp [Lax235315Proofs.Construction.ListCrossing.insertAfter,
        Lax457868Proofs.TwinExpansion.insertAfter, ih]

/-- The old list-ordered restoration is definitionally the same sequence of
insertions as the indexed refined round restoration. -/
lemma restoreAfter_eq_insertAllTwins {α : Type*} [DecidableEq α]
    (representative : α → α) (small removed : List α) :
    Lax235315Proofs.Construction.ConcreteReconstruction.restoreAfter
        representative small removed =
      Lax457868Proofs.TwinExpansion.insertAllTwins representative small removed := by
  induction removed generalizing small with
  | nil => rfl
  | cons new rest ih =>
      simp only [Lax235315Proofs.Construction.ConcreteReconstruction.restoreAfter_cons,
        Lax457868Proofs.TwinExpansion.insertAllTwins]
      rw [insertAfter_eq]
      exact ih _

/-- A refined sample and two actual source trace partitions give a checked
original reduction. The larger list is exactly `restoreAfter` from the source
reconstruction, while its crossing conclusion follows from the checked
near-twin bound and the original generic crossing induction. -/
lemma restoreAfter_reduction {n c k : ℕ} {G : SimpleGraph (Fin n)}
    (A B W A' B' : Finset (Fin n))
    (hsample : IsRefinedSample
      (Lax457868Proofs.SamplerContract.neighborhoodFamily B
        (Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G A))
      (A : Set (Fin n)) (W : Set (Fin n))
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k)
    (hWA : W ⊆ A)
    (hB : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    (hA : TracePartition G (A : Set (Fin n)) (B' : Set (Fin n))
      (A' : Set (Fin n)))
    (small removed : List (Fin n))
    (hsmall : Enumerates (A' : Set (Fin n)) small)
    (hremoved : Enumerates ((A : Set (Fin n)) \ (A' : Set (Fin n))) removed)
    (hsmallBound : ∀ b ∈ (B' : Set (Fin n)),
      Lax235315Proofs.Construction.ListCrossing.crossingCount
        (G.neighborSet b) small ≤ (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) :
    ∃ _reduction : Reduction G k (A : Set (Fin n)) (B : Set (Fin n))
      (A' : Set (Fin n)) (B' : Set (Fin n)) small
      (Lax235315Proofs.Construction.ConcreteReconstruction.restoreAfter
        hA.representative small removed),
      ∀ b ∈ (B : Set (Fin n)),
        Lax235315Proofs.Construction.ListCrossing.crossingCount
          (G.neighborSet b)
          (Lax235315Proofs.Construction.ConcreteReconstruction.restoreAfter
            hA.representative small removed) ≤
            (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2) + 2 * k := by
  classical
  let contraction := traceContractionOfVerifiedPartitions G A B W B' A' hWA hB hA
  obtain ⟨hbig, hexpands⟩ :=
    TracePartition.restoreAfter_nonrepresentatives hA hsmall hremoved
  have hnear (b : Fin n) (hb : b ∈ B) :
      ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
        (G.neighborSet (hB.representative b) ∩ (A : Set (Fin n)))).ncard ≤ k := by
    have hbound := near_twin_restricted_ncard
      (G := G) A B W hsample contraction b hb
    have hrep : contraction.bChoice.representative b = hB.representative b := by
      rfl
    rw [hrep] at hbound
    have hset :
        ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
          (G.neighborSet (hB.representative b) ∩ (A : Set (Fin n)))) =
        (((Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G A b : Finset (Fin n)) :
            Set (Fin n)) \
          (Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G A
            (hB.representative b) : Set (Fin n))) ∪
        (((Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G A
            (hB.representative b) : Finset (Fin n)) : Set (Fin n)) \
          (Lax457868Proofs.GraphTraceBounds.finiteNeighborhood G A b : Set (Fin n))) := by
      ext v
      simp [Set.symmDiff_def, Lax457868Proofs.GraphTraceBounds.finiteNeighborhood,
        SimpleGraph.mem_neighborSet]
      all_goals aesop
    rw [hset.symm] at hbound
    exact hbound
  let reduction : Reduction G k (A : Set (Fin n)) (B : Set (Fin n))
      (A' : Set (Fin n)) (B' : Set (Fin n)) small
      (Lax235315Proofs.Construction.ConcreteReconstruction.restoreAfter
        hA.representative small removed) := {
    small_enumerates := hsmall
    big_enumerates := hbig
    expands := hexpands
    representative := hB.representative
    representative_mem := hB.representative_mem
    near := hnear
  }
  refine ⟨reduction, ?_⟩
  intro b hb
  exact reduction.crossingCount_le G hsmallBound b hb

end Lax457868Proofs.VerifiedReconstructionBridge
