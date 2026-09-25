import Lax235315Proofs.Construction.GraphSampling
import Lax235315Proofs.Construction.PaperRun
import Mathlib.Data.Finset.Dedup

/-!
The ideal-sampling execution of Figure 1.  This module connects the finite
bad-sample event to the successful reconstruction certificate, independently
of the particular random-bit implementation.
-/

namespace Lax235315Proofs.Construction.AbstractAlgorithm

open scoped symmDiff
open Finset
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.PaperRun
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Canonical finite representative side of a trace quotient. -/
def quotient (G : SimpleGraph (Fin n)) (V S : Finset (Fin n)) :
    Finset (Fin n) :=
  (Set.toFinite
    (canonicalRepresentatives G (V : Set (Fin n)) (S : Set (Fin n)))).toFinset

@[simp] theorem coe_quotient (V S : Finset (Fin n)) :
    (quotient G V S : Set (Fin n)) =
      canonicalRepresentatives G (V : Set (Fin n)) (S : Set (Fin n)) := by
  simp [quotient]

def quotientPartition (V S : Finset (Fin n)) :
    TracePartition G (V : Set (Fin n)) (S : Set (Fin n))
      (quotient G V S : Set (Fin n)) := by
  simpa using canonicalTracePartition G (V : Set (Fin n)) (S : Set (Fin n))

theorem quotient_nonempty {V S : Finset (Fin n)} (hV : V.Nonempty) :
    (quotient G V S).Nonempty := by
  have h := (quotientPartition G V S).reps_nonempty G (by simpa using hV)
  obtain ⟨v, hv⟩ := h
  exact ⟨v, by simpa [quotient] using hv⟩

theorem sampleSize_pos {a c : ℕ} (hc : 1 ≤ c) (ha : 0 < a) :
    0 < sampleSize a c := by
  have h := le_mul_sampleSize (a := a) hc
  by_contra hs
  have hz : sampleSize a c = 0 := Nat.eq_zero_of_not_pos hs
  rw [hz] at h
  simp at h
  omega

/-- A sequence of ideal samples, each of the prescribed size and outside the
bad family for its current state. -/
inductive GoodSampleRun (c L : ℕ) :
    ℕ → Finset (Fin n) → Finset (Fin n) → Prop
  | base {A B : Finset (Fin n)}
      (small : A.card ≤ 12 * c ^ 2 * L) :
      GoodSampleRun c L 0 A B
  | step {rounds : ℕ} {A B W : Finset (Fin n)}
      (large : 12 * c ^ 2 * L < A.card)
      (B_nonempty : B.Nonempty)
      (sample_subset : W ⊆ A)
      (sample_card : W.card = sampleSize A.card c)
      (good : W ∉ familyBadSamples (traceFamily G A B) id A c L)
      (tail : GoodSampleRun c L rounds
        (quotient G A (quotient G B W)) (quotient G B W)) :
      GoodSampleRun c L (rounds + 1) A B

/-- Outside the bad-sample event, every class representative passes the
paper's near-twin verification. -/
theorem near_of_good_sample {c L : ℕ} {A B W : Finset (Fin n)}
    (hWsub : W ⊆ A)
    (hWcard : W.card = sampleSize A.card c)
    (hgood : W ∉ familyBadSamples (traceFamily G A B) id A c L) :
    let hB := quotientPartition G B W
    ∀ b ∈ (B : Set (Fin n)),
      ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
        (G.neighborSet (hB.representative b) ∩
          (A : Set (Fin n)))).ncard ≤ 6 * c ^ 2 * L := by
  dsimp
  intro b hb
  by_contra hfar
  apply hgood
  apply failed_near_check_mem_familyBadSamples G hWsub hWcard
    (quotientPartition G B W) (by simpa using hb)
  omega

/-- Every good ideal-sample run produces a successful paper run and its
concrete vertex list. -/
theorem GoodSampleRun.exists_successfulRun {c L rounds : ℕ}
    (hc : 1 ≤ c) {A B : Finset (Fin n)}
    (h : GoodSampleRun G c L rounds A B) :
    ∃ l : List (Fin n),
      SuccessfulRun G c L rounds (A : Set (Fin n)) (B : Set (Fin n)) l := by
  induction h with
  | @base A B hsmall =>
      refine ⟨A.toList, SuccessfulRun.base ?_ ?_⟩
      · exact ⟨A.nodup_toList, by simp⟩
      · simpa using hsmall
  | @step rounds A B W large hBne hWsub hWcard hgood tail ih =>
      let B' := quotient G B W
      let A' := quotient G A B'
      let hBp := quotientPartition G B W
      let hAp := quotientPartition G A B'
      obtain ⟨small, htail⟩ := ih
      have hWne : W.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hzero
        have hApos : 0 < A.card := by omega
        have hspos := sampleSize_pos hc hApos
        rw [hzero] at hWcard
        simp at hWcard
        omega
      have hnear : ∀ b ∈ (B : Set (Fin n)),
          ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
            (G.neighborSet (hBp.representative b) ∩
              (A : Set (Fin n)))).ncard ≤ 6 * c ^ 2 * L :=
        near_of_good_sample G hWsub hWcard hgood
      have hsmall : Enumerates (A' : Set (Fin n)) small := by
        exact (htail.toCertifiedRun G).enumerates G
      obtain ⟨big, hred⟩ := exists_reduction_of_partitions G hBp hAp hnear hsmall
      refine ⟨big, SuccessfulRun.step (by simpa using large)
        (by simpa using hBne) (by simpa using hWne) ?_ ?_ hBp hAp hnear
        hred.some htail⟩
      · intro v hv
        exact hWsub (by simpa using hv)
      · simpa using hWcard

end

end Lax235315Proofs.Construction.AbstractAlgorithm
