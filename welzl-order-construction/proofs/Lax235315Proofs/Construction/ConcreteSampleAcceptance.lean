import Lax235315Proofs.Construction.GoodSampleCertificate
import Lax235315Proofs.Construction.RoundSamplePartitionSource
import Lax235315Proofs.Construction.NearCounterCorrectness
import Mathlib.Tactic

/-! A sample outside the graph bad-sample event forces the literal round
certificate's `good` flag to remain set. -/

namespace Lax235315Proofs.Construction.ConcreteSampleAcceptance

open scoped symmDiff
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.GoodSampleCertificate
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.RoundSamplePartitionSource
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions

noncomputable section

/-- If the actual sample is good for the current `A`/`B`, the concrete
certificate run accepts it. `sampleFin` is the same numeric source sample
viewed as a finite subset of `Fin n`; `sampleSet` records that correspondence.
The execution API currently requires the subset and cardinality facts as
explicit inputs. -/
lemma preparePartitionsAndVerify_accepts_good_sample
    {B n c L bound cost : ℕ} {G : SimpleGraph (Fin n)}
    {σ σ' : Env} {activeA activeB repB : ℕ → ℕ}
    {sample : Finset ℕ} {sampleFin : Finset (Fin n)}
    {R : Finset ℕ}
    (hrun : Run B preparePartitionsAndVerify σ σ' cost)
    (hgoodInput : σ.vars "good" = 1)
    (hbound : bound = 6 * c ^ 2 * L)
    (hpart : ConcreteTracePartition G activeB (finSetAsSet sample) R repB)
    (hsampleSet : (sampleFin : Set (Fin n)) = finSetAsSet sample)
    (hsampleSub : sampleFin ⊆ activeFinset (n := n) activeA)
    (hsampleCard : sampleFin.card = sampleSize
      (activeFinset (n := n) activeA).card c)
    (hbadOutside : sampleFin ∉ familyBadSamples
      (traceFamily G (activeFinset (n := n) activeA)
        (activeFinset (n := n) activeB)) id
        (activeFinset (n := n) activeA) c L)
    (hgoodIff : σ'.vars "good" = 1 ↔
      σ.vars "good" = 1 ∧
        ∀ (v : Fin n) (hv : activeB v.val = 1),
          ((G.neighborSet v ∩ (activeFinset (n := n) activeA : Set (Fin n))) ∆
            (G.neighborSet (hpart.partition.representative v) ∩
              (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound) :
    Run B preparePartitionsAndVerify σ σ' cost ∧ σ'.vars "good" = 1 := by
  let partitionFin : TracePartition G {v : Fin n | activeB v.val = 1}
      (sampleFin : Set (Fin n)) (finSetAsSet R) := {
      representative := hpart.partition.representative
      representative_mem := hpart.partition.representative_mem
      same_trace := by
        intro v hv
        simpa [hsampleSet] using hpart.partition.same_trace v
          hv
      reps_mem := hpart.partition.reps_mem
      reps_separated := by
        intro u hu v hv heq
        exact hpart.partition.reps_separated hu hv
          (by simpa [hsampleSet] using heq) }
  have hrepFn : partitionFin.representative = hpart.partition.representative := rfl
  let hpartFin : ConcreteTracePartition G activeB
      (sampleFin : Set (Fin n)) R repB := by
    refine ⟨partitionFin, ?_⟩
    intro v hv
    simpa [hrepFn] using hpart.representative_val v hv
  have hnear := near_of_good_concrete_partition G hsampleSub hsampleCard
    hbadOutside hpartFin
  have hnearBound :
      ∀ (v : Fin n) (hv : activeB v.val = 1),
        ((G.neighborSet v ∩ (activeFinset (n := n) activeA : Set (Fin n))) ∆
          (G.neighborSet (hpart.partition.representative v) ∩
            (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound := by
    intro v hv
    have hvNear := hnear v hv
    have hrepEq : hpart.partition.representative v =
        (⟨repB v.val, hpartFin.rep_lt v.isLt hv⟩ : Fin n) := by
      apply Fin.ext
      simpa [hrepFn] using hpartFin.representative_val v hv
    rw [← hrepEq] at hvNear
    simpa [hbound] using hvNear
  exact ⟨hrun, hgoodIff.mpr ⟨hgoodInput, hnearBound⟩⟩

end

end Lax235315Proofs.Construction.ConcreteSampleAcceptance
