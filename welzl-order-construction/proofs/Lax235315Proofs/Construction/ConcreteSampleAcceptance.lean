import Lax235315Proofs.Construction.GoodSampleCertificate
import Lax235315Proofs.Construction.RoundSamplePartitionSource
import Lax235315Proofs.Construction.NearCounterCorrectness
import Lax235315Proofs.Construction.RoundInvariant
import Lax235315Proofs.Construction.MarkingMath
import Lax235315Proofs.Construction.ActiveBookkeeping
import Lax235315Proofs.Construction.RoundPartitionSource
import Lax11.GraphEncoding
import Mathlib.Tactic

/-! A sample outside the graph bad-sample event forces the literal round
certificate's `good` flag to remain set. -/

namespace Lax235315Proofs.Construction.ConcreteSampleAcceptance

open scoped symmDiff
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.GoodSampleCertificate
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.PartitionCompleteSource
open Lax235315Proofs.Construction.RoundSamplePartitionSource
open Lax235315Proofs.Construction.RoundPartitionSource
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.WelzlProgram

noncomputable section

set_option maxRecDepth 4096

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

/-- Frontier-level form: the actual source run theorem supplies the exact
good-flag specification, so callers only provide the current sample facts. -/
lemma frontier_preparePartitionsAndVerify_accepts_good_sample
    {B c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    {σ : Env} {sample : Finset ℕ} {sampleFin : Finset (Fin n)}
    (hx : EncodesGraph x n G)
    (h : Frontier B c n x σ)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hcsq : σ.vars "csq" = c ^ 2)
    (hbound : σ.vars "nearBound" = 6 * c ^ 2 * Nat.clog 2 n)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c)
      (view σ "ord") sample)
    (hsampleRange : ∀ v ∈ sample, v < n)
    (hsampleSet : (sampleFin : Set (Fin n)) = finSetAsSet sample)
    (hsampleSub : sampleFin ⊆ activeFinset (n := n) (view σ "activeA"))
    (hsampleCard : sampleFin.card = sampleSize
      (activeFinset (n := n) (view σ "activeA")).card c)
    (hbadOutside : sampleFin ∉ familyBadSamples
      (traceFamily G (activeFinset (n := n) (view σ "activeA"))
        (activeFinset (n := n) (view σ "activeB"))) id
        (activeFinset (n := n) (view σ "activeA")) c (Nat.clog 2 n))
    (hnB : 2 * n + 1 < B)
    (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B)
    (hboundB : 6 * c ^ 2 * Nat.clog 2 n < B) :
    ∃ σ', Run B buildReductionCertificate σ σ'
        (2200 * (x.length + 1)) ∧ σ'.vars "good" = 1 := by
  have arr (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt") (h₃ : a ≠ "count") :=
    h.workspace.vertex_array h₁ h₂ h₃
  have hactiveAB : ∀ v < n, view σ "activeA" v < B := by
    intro v hv
    exact h.workspace.value_bound (by rw [h.workspace.lengths]; exact hv)
  have hactiveBB : ∀ v < n, view σ "activeB" v < B := by
    intro v hv
    exact h.workspace.value_bound (by rw [h.workspace.lengths]; exact hv)
  have ha : 0 < σ.vars "acount" := by
    rw [h.activeCount]
    exact Finset.card_pos.mpr (h.nonemptyA (by omega))
  have haN : σ.vars "acount" ≤ n := by
    rw [h.activeCount]
    exact activeVertices_card_le _ _
  obtain ⟨τ, currentB, labelB', repClassB', repsB', nextB', repB', R,
      partB, currentA, labelA', repClassA', repsA', nextA', repA', S,
      hrun, hBdata, hAdata, hApart, hnear, hred, hnextBCount,
      hnextACount, hactiveA, hactiveB, hrepsA, hrepsB, hnextA,
      hnextB, hrepA, hrepB, hgoodIff⟩ :=
    preparePartitionsAndVerify_run_full hx rfl h.workspace.vertices rfl hcsq
      hbound (h.workspace.bounded.vars "good") h.workspace.offsets
      h.workspace.targets
      (arr "activeA" (by decide) (by decide) (by decide))
      (arr "activeB" (by decide) (by decide) (by decide))
      (arr "ord" (by decide) (by decide) (by decide))
      (arr "classB" (by decide) (by decide) (by decide))
      (arr "classA" (by decide) (by decide) (by decide))
      (arr "classSize" (by decide) (by decide) (by decide))
      (arr "markedCount" (by decide) (by decide) (by decide))
      (arr "stamp" (by decide) (by decide) (by decide))
      (arr "marked" (by decide) (by decide) (by decide))
      (arr "touched" (by decide) (by decide) (by decide))
      (arr "split" (by decide) (by decide) (by decide))
      (arr "repClass" (by decide) (by decide) (by decide))
      (arr "repsB" (by decide) (by decide) (by decide))
      (arr "nextB" (by decide) (by decide) (by decide))
      (arr "repB" (by decide) (by decide) (by decide))
      (arr "repsA" (by decide) (by decide) (by decide))
      (arr "nextA" (by decide) (by decide) (by decide))
      (arr "repA" (by decide) (by decide) (by decide))
      (arr "degree" (by decide) (by decide) (by decide))
      (arr "inter" (by decide) (by decide) (by decide))
      (arr "neighbors" (by decide) (by decide) (by decide))
      henum hsampleRange (h.nonemptyA (by omega)) (h.nonemptyB (by omega))
      hc ha haN hactiveAB hactiveBB hnB (by simpa using htargetB) hdenomB
      (by simpa using hboundB)
  have hRr : ∀ v ∈ R, v < n := fun v hv =>
    (mem_activeVertices.mp (hBdata.reps_processed hv)).1
  have hRcard : R.card ≤ n :=
    (Finset.card_le_card hBdata.reps_processed).trans
      (activeVertices_card_le _ _)
  have hcostA := partitionCost_le_input hx
    ((sampleSize_le_self hc ha).trans haN)
    (PrefixEnumerates.entry_lt henum hsampleRange)
    henum.injective_on_prefix
  have hcostB := partitionCost_le_input hx hRcard
    (PrefixEnumerates.entry_lt hBdata.enum hRr)
    hBdata.enum.injective_on_prefix
  have hcost : Run B buildReductionCertificate σ τ
      (2200 * (x.length + 1)) := by
    apply hrun.mono
    have hxlen := hx.length_eq
    omega
  have haccept := preparePartitionsAndVerify_accepts_good_sample
    hrun h.success rfl partB hsampleSet hsampleSub hsampleCard hbadOutside
    hgoodIff
  exact ⟨τ, hcost, haccept.2⟩

end

end Lax235315Proofs.Construction.ConcreteSampleAcceptance
