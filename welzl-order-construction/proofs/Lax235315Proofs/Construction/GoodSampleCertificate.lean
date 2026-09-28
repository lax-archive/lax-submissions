import Lax235315Proofs.Construction.GraphSampling
import Lax235315Proofs.Construction.NearCounterCorrectness
import Lax235315Proofs.Construction.PartitionResult
import Mathlib.Tactic

/-! Acceptance of a sample outside the finite bad-sample event, for arbitrary
trace partitions and then for the representatives stored by a concrete run. -/

namespace Lax235315Proofs.Construction.GoodSampleCertificate

open scoped symmDiff
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Every partition of the sample test set passes the near check when the
sample lies outside the associated bad-sample family. -/
lemma near_of_good_sample_partition {c L : ℕ} {A B W B' : Finset (Fin n)}
    (hWsub : W ⊆ A)
    (hWcard : W.card = sampleSize A.card c)
    (hpart : TracePartition G (B : Set (Fin n)) (W : Set (Fin n))
      (B' : Set (Fin n)))
    (hgood : W ∉ familyBadSamples (traceFamily G A B) id A c L) :
    ∀ b ∈ (B : Set (Fin n)),
      ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
        (G.neighborSet (hpart.representative b) ∩
          (A : Set (Fin n)))).ncard ≤ 6 * c ^ 2 * L := by
  intro b hb
  by_contra hfar
  apply hgood
  apply failed_near_check_mem_familyBadSamples (G := G) (c := c) (L := L)
    hWsub hWcard hpart (by simpa using hb)
  omega

/-- Specialization to the active vertices and the representative function
stored by a concrete trace partition. -/
lemma near_of_good_concrete_partition {c L : ℕ}
    {A W : Finset (Fin n)} {R : Finset ℕ}
    {active repOf : ℕ → ℕ}
    (hWsub : W ⊆ A)
    (hWcard : W.card = sampleSize A.card c)
    (hgood : W ∉ familyBadSamples
      (traceFamily G A (activeFinset active)) id A c L)
    (hpart : ConcreteTracePartition G active (W : Set (Fin n)) R repOf) :
    ∀ (b : Fin n) (hb : active b.val = 1),
      ((G.neighborSet b ∩ (A : Set (Fin n))) ∆
        (G.neighborSet
          (⟨repOf b.val, hpart.rep_lt b.isLt hb⟩ : Fin n) ∩
          (A : Set (Fin n)))).ncard ≤ 6 * c ^ 2 * L := by
  let Rfin : Finset (Fin n) := Finset.univ.filter fun v => v.val ∈ R
  have hRfin : (Rfin : Set (Fin n)) = finSetAsSet R := by
    ext v
    simp [Rfin, finSetAsSet]
  let htrace : TracePartition G (activeFinset (n := n) active : Set (Fin n))
      (W : Set (Fin n)) (Rfin : Set (Fin n)) := {
    representative := hpart.partition.representative
    representative_mem := by
      intro v hv
      have hv' : v ∈ {x : Fin n | active x.val = 1} := by
        simpa [activeFinset] using hv
      have hr := hpart.partition.representative_mem v hv'
      simpa [hRfin] using hr
    same_trace := by
      intro v hv
      apply hpart.partition.same_trace
      simpa [activeFinset] using hv
    reps_mem := by
      intro r hr
      have hr' : r ∈ finSetAsSet R := by simpa [hRfin] using hr
      have hactive := hpart.partition.reps_mem hr'
      simpa [activeFinset] using hactive
    reps_separated := by
      intro u hu v hv heq
      apply hpart.partition.reps_separated
      · simpa [hRfin] using hu
      · simpa [hRfin] using hv
      · exact heq }
  have hnear := near_of_good_sample_partition G hWsub hWcard htrace hgood
  intro b hb
  have hactive : active b.val = 1 := hb
  let r : Fin n := ⟨repOf b.val, hpart.rep_lt b.isLt hactive⟩
  have hr : hpart.partition.representative b = r := by
    apply Fin.ext
    exact hpart.representative_val b hactive
  have hr' : htrace.representative b = r := by
    change hpart.partition.representative b = r
    exact hr
  simpa [r, hr', activeFinset] using
    hnear b (by simp [activeFinset, hb])

end

end Lax235315Proofs.Construction.GoodSampleCertificate
