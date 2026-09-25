import Lax235315Proofs.Construction.RoundPartitionSource
import Lax235315Proofs.Construction.VerifyNearSource
import Mathlib.Tactic

/-! Source-level composition of the second trace partition and the batched
near-twin verifier in one reduction round. -/

namespace Lax235315Proofs.Construction.RoundVerifySource

open scoped symmDiff
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.NearSweepMath
open Lax235315Proofs.Construction.PartitionCompleteSource
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.RoundPartitionSource
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.VerifyNearSource
open Lax235315Proofs.Construction.WelzlProgram

noncomputable section

set_option maxRecDepth 10000

/-- Concrete representative arrays, their two trace partitions, and a
successful near check already constitute the abstract reduction certificate
used in the crossing-number proof. -/
theorem exists_reduction_of_concrete_partitions
    {n k : ℕ} {G : SimpleGraph (Fin n)}
    {activeA activeB repA repB : ℕ → ℕ} {W R S : Finset ℕ}
    (hB : ConcreteTracePartition G activeB (finSetAsSet W) R repB)
    (hA : ConcreteTracePartition G activeA (finSetAsSet R) S repA)
    (hnear : ∀ b ∈ ({v : Fin n | activeB v.val = 1} : Set (Fin n)),
      ((G.neighborSet b ∩ {v : Fin n | activeA v.val = 1}) ∆
        (G.neighborSet (hB.partition.representative b) ∩
          {v : Fin n | activeA v.val = 1})).ncard ≤ k)
    {small : List (Fin n)} (hsmall : Enumerates (finSetAsSet S) small) :
    ∃ big, Nonempty (Reduction G k
      {v : Fin n | activeA v.val = 1}
      {v : Fin n | activeB v.val = 1}
      (finSetAsSet S) (finSetAsSet R) small big) := by
  exact exists_reduction_of_partitions G hB.partition hA.partition hnear hsmall

/-- The literal suffix consisting of the second partition and the complete
near-twin verification. -/
def secondPartitionAndVerify : Com :=
  seqs [
    partition "activeA" "repsB" "nextBCount" "classA"
      "repsA" "nextA" "repA" "nextACount",
    verifyNear]

/-- The second trace partition and the subsequent source-level checker use
the same concrete `repB` map as the first trace-partition certificate. Thus a
successful checker result is already the near condition needed by the paper. -/
theorem secondPartitionAndVerify_run
    {B n targetCap current bound : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ}
    {activeA activeB labelB repClassB repsB nextB repB
      classA classSize markedCount stamp marked touched split oldRepClass
      repsA nextA repA degree inter neighbors : ℕ → ℕ}
    {W R : Finset ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n)
    (hnextBCount : σ.vars "nextBCount" = R.card)
    (hbound : σ.vars "nearBound" = bound) (hgoodB : σ.vars "good" < B)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactiveAArray : σ.arrs "activeA" = arrOf n activeA)
    (hactiveBArray : σ.arrs "activeB" = arrOf n activeB)
    (hrepsB : σ.arrs "repsB" = arrOf n repsB)
    (hrepB : σ.arrs "repB" = arrOf n repB)
    (hclassA : σ.arrs "classA" = arrOf n classA)
    (hclassSize : σ.arrs "classSize" = arrOf n classSize)
    (hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hsplit : σ.arrs "split" = arrOf n split)
    (hrepClass : σ.arrs "repClass" = arrOf n oldRepClass)
    (hrepsA : σ.arrs "repsA" = arrOf n repsA)
    (hnextA : σ.arrs "nextA" = arrOf n nextA)
    (hrepA : σ.arrs "repA" = arrOf n repA)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hneighbors : σ.arrs "neighbors" = arrOf n neighbors)
    (hBdata : RepData n current n activeB labelB repClassB repsB nextB R)
    (hBpartition : ConcreteTracePartition G activeB (finSetAsSet W) R repB)
    (hactiveANonempty : (activeVertices n activeA).Nonempty)
    (hactiveAB : ∀ v < n, activeA v < B)
    (hactiveBB : ∀ v < n, activeB v < B)
    (hnB : 2 * n + 1 < B) (htargetCapB : targetCap < B)
    (hboundB : bound < B) :
    ∃ σ' current' labelA repClass' repsA' nextA' repA' S,
      Run B secondPartitionAndVerify σ σ'
        (partitionCost x repsB n R.card + 400 * (n + targetCap + 1)) ∧
      RepData n current' n activeA labelA repClass' repsA' nextA' S ∧
      Nonempty (ConcreteTracePartition G activeA (finSetAsSet R) S repA') ∧
      (σ'.vars "good" = 1 →
        ∀ (v : Fin n) (hv : activeB v.val = 1),
          ((G.neighborSet v ∩
              (activeFinset (n := n) activeA : Set (Fin n))) ∆
            (G.neighborSet (hBpartition.partition.representative v) ∩
              (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound) := by
  obtain ⟨σ₁, current', labelA, repClass', repsA', nextA', repA', S,
      rpartition, hnextACount, hactiveA₁, hclassA₁, hrepClass₁, hrepsA₁,
      hnextA₁, hrepA₁, hAdata, hAmap, hApartition⟩ :=
    secondPartition_run hx htargetCap hn hnextBCount hoff htarget
      hactiveAArray hrepsB hclassA hclassSize hmarkedCount hstamp hmarked
      htouched hsplit hrepClass hrepsA hnextA hrepA hBdata hactiveANonempty
      (by omega) htargetCapB (by omega) hactiveAB
  have hn₁ : σ₁.vars "n" = n := by
    rw [rpartition.frame_var "n" (by decide), hn]
  have hbound₁ : σ₁.vars "nearBound" = bound := by
    rw [rpartition.frame_var "nearBound" (by decide), hbound]
  have hgoodB₁ : σ₁.vars "good" < B := by
    rw [rpartition.frame_var "good" (by decide)]
    exact hgoodB
  have hoff₁ : σ₁.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [rpartition.frame_arr "off" (by decide), hoff]
  have htarget₁ : σ₁.arrs "tgt" = arrOf targetCap (target x) := by
    rw [rpartition.frame_arr "tgt" (by decide), htarget]
  have hactiveB₁ : σ₁.arrs "activeB" = arrOf n activeB := by
    rw [rpartition.frame_arr "activeB" (by decide), hactiveBArray]
  have hrepB₁ : σ₁.arrs "repB" = arrOf n repB := by
    rw [rpartition.frame_arr "repB" (by decide), hrepB]
  have hdegree₁ : σ₁.arrs "degree" = arrOf n degree := by
    rw [rpartition.frame_arr "degree" (by decide), hdegree]
  have hinter₁ : σ₁.arrs "inter" = arrOf n inter := by
    rw [rpartition.frame_arr "inter" (by decide), hinter]
  have hneighbors₁ : σ₁.arrs "neighbors" = arrOf n neighbors := by
    rw [rpartition.frame_arr "neighbors" (by decide), hneighbors]
  have hstampLen : (σ₁.arrs "stamp").length = n := by
    rw [run_array_length_eq rpartition "stamp", hstamp, length_arrOf]
  obtain ⟨stamp₁, hstamp₁⟩ := exists_arrOf_of_length hstampLen
  obtain ⟨σ₂, rverify, hnear⟩ := verifyNear_run hx htargetCap
    (fun _ _ => rfl) (fun _ _ => rfl) hn₁ hbound₁ hgoodB₁ hoff₁ htarget₁ hactiveA₁ hactiveB₁
    hrepB₁ hdegree₁ hinter₁ hstamp₁ hneighbors₁ hactiveAB hactiveBB
    (fun v hvn hv => hBpartition.rep_lt hvn hv)
    (fun v hvn hv => hBpartition.rep_active hvn hv)
    hnB htargetCapB hboundB
  refine ⟨σ₂, current', labelA, repClass', repsA', nextA', repA', S,
    ?_, hAdata, hApartition, ?_⟩
  · simpa [secondPartitionAndVerify, seqs] using rpartition.seq rverify
  · intro hgood v hv
    have h := hnear hgood v hv
    have hrep : (⟨repB v.val, hBpartition.rep_lt v.isLt hv⟩ : Fin n) =
        hBpartition.partition.representative v := by
      apply Fin.ext
      exact (hBpartition.representative_val v hv).symm
    simpa [hrep] using h

end

end Lax235315Proofs.Construction.RoundVerifySource
