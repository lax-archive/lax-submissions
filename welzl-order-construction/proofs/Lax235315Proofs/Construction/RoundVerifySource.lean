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
lemma exists_reduction_of_concrete_partitions
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
lemma secondPartitionAndVerify_run_full
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
    (hnextBArray : σ.arrs "nextB" = arrOf n nextB)
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
              (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound) ∧
      σ'.vars "nextBCount" = R.card ∧
      σ'.vars "nextACount" = S.card ∧
      σ'.arrs "activeA" = arrOf n activeA ∧
      σ'.arrs "activeB" = arrOf n activeB ∧
      σ'.arrs "repsA" = arrOf n repsA' ∧
      σ'.arrs "repsB" = arrOf n repsB ∧
      σ'.arrs "nextA" = arrOf n nextA' ∧
      σ'.arrs "nextB" = arrOf n nextB ∧
      σ'.arrs "repA" = arrOf n repA' ∧
      σ'.arrs "repB" = arrOf n repB ∧
      (σ'.vars "good" = 1 ↔ σ.vars "good" = 1 ∧
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
  have hgoodValue₁ : σ₁.vars "good" = σ.vars "good" := by
    rw [rpartition.frame_var "good" (by decide)]
  have hoff₁ : σ₁.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [rpartition.frame_arr "off" (by decide), hoff]
  have htarget₁ : σ₁.arrs "tgt" = arrOf targetCap (target x) := by
    rw [rpartition.frame_arr "tgt" (by decide), htarget]
  have hactiveB₁ : σ₁.arrs "activeB" = arrOf n activeB := by
    rw [rpartition.frame_arr "activeB" (by decide), hactiveBArray]
  have hrepB₁ : σ₁.arrs "repB" = arrOf n repB := by
    rw [rpartition.frame_arr "repB" (by decide), hrepB]
  have hnextB₁ : σ₁.arrs "nextB" = arrOf n nextB := by
    rw [rpartition.frame_arr "nextB" (by decide), hnextBArray]
  have hrepsB₁ : σ₁.arrs "repsB" = arrOf n repsB := by
    rw [rpartition.frame_arr "repsB" (by decide), hrepsB]
  have hnextBCount₁ : σ₁.vars "nextBCount" = R.card := by
    rw [rpartition.frame_var "nextBCount" (by decide), hnextBCount]
  have hdegree₁ : σ₁.arrs "degree" = arrOf n degree := by
    rw [rpartition.frame_arr "degree" (by decide), hdegree]
  have hinter₁ : σ₁.arrs "inter" = arrOf n inter := by
    rw [rpartition.frame_arr "inter" (by decide), hinter]
  have hneighbors₁ : σ₁.arrs "neighbors" = arrOf n neighbors := by
    rw [rpartition.frame_arr "neighbors" (by decide), hneighbors]
  have hstampLen : (σ₁.arrs "stamp").length = n := by
    rw [run_array_length_eq rpartition "stamp", hstamp, length_arrOf]
  obtain ⟨stamp₁, hstamp₁⟩ := exists_arrOf_of_length hstampLen
  obtain ⟨σ₂, rverify, hnearVerify, hgoodVerify⟩ := verifyNear_run_full hx htargetCap
    (fun _ _ => rfl) (fun _ _ => rfl) hn₁ hbound₁ hgoodB₁ hoff₁ htarget₁ hactiveA₁ hactiveB₁
    hrepB₁ hdegree₁ hinter₁ hstamp₁ hneighbors₁ hactiveAB hactiveBB
    (fun v hvn hv => hBpartition.rep_lt hvn hv)
    (fun v hvn hv => hBpartition.rep_active hvn hv)
    hnB htargetCapB hboundB
  have hnextB₂ : σ₂.arrs "nextB" = arrOf n nextB := by
    rw [rverify.frame_arr "nextB" (by decide), hnextB₁]
  have hrepsB₂ : σ₂.arrs "repsB" = arrOf n repsB := by
    rw [rverify.frame_arr "repsB" (by decide), hrepsB₁]
  have hnextBCount₂ : σ₂.vars "nextBCount" = R.card := by
    rw [rverify.frame_var "nextBCount" (by decide), hnextBCount₁]
  have hcount₂ : σ₂.vars "nextACount" = S.card := by
    rw [rverify.frame_var "nextACount" (by decide), hnextACount]
  have hactiveA₂ : σ₂.arrs "activeA" = arrOf n activeA := by
    rw [rverify.frame_arr "activeA" (by decide), hactiveA₁]
  have hactiveB₂ : σ₂.arrs "activeB" = arrOf n activeB := by
    rw [rverify.frame_arr "activeB" (by decide), hactiveB₁]
  have hrepsA₂ : σ₂.arrs "repsA" = arrOf n repsA' := by
    rw [rverify.frame_arr "repsA" (by decide), hrepsA₁]
  have hnextA₂ : σ₂.arrs "nextA" = arrOf n nextA' := by
    rw [rverify.frame_arr "nextA" (by decide), hnextA₁]
  have hrepA₂ : σ₂.arrs "repA" = arrOf n repA' := by
    rw [rverify.frame_arr "repA" (by decide), hrepA₁]
  have hrepB₂ : σ₂.arrs "repB" = arrOf n repB := by
    rw [rverify.frame_arr "repB" (by decide), hrepB₁]
  let hnearCondition : Prop := ∀ (v : Fin n) (hv : activeB v.val = 1),
      ((G.neighborSet v ∩
          (activeFinset (n := n) activeA : Set (Fin n))) ∆
        (G.neighborSet (hBpartition.partition.representative v) ∩
          (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound
  have hnearRepB :
      (∀ (v : Fin n) (hv : activeB v.val = 1),
        ((G.neighborSet v ∩
            (activeFinset (n := n) activeA : Set (Fin n))) ∆
          (G.neighborSet ⟨repB v.val, hBpartition.rep_lt v.isLt hv⟩ ∩
            (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound) ↔
      hnearCondition := by
    constructor
    · intro h v hv
      have h' := h v hv
      have hrep : (⟨repB v.val, hBpartition.rep_lt v.isLt hv⟩ : Fin n) =
          hBpartition.partition.representative v := by
        apply Fin.ext
        exact (hBpartition.representative_val v hv).symm
      simpa [hrep] using h'
    · intro h v hv
      have h' := h v hv
      have hrep : (⟨repB v.val, hBpartition.rep_lt v.isLt hv⟩ : Fin n) =
          hBpartition.partition.representative v := by
        apply Fin.ext
        exact (hBpartition.representative_val v hv).symm
      simpa [hrep] using h'
  have hgoodExact : σ₂.vars "good" = 1 ↔
      σ.vars "good" = 1 ∧ hnearCondition := by
    constructor
    · intro hgood
      obtain ⟨hgoodIn, hnearIn⟩ := hgoodVerify.mp hgood
      refine ⟨?_, hnearRepB.mp hnearIn⟩
      rw [← hgoodValue₁]
      exact hgoodIn
    · rintro ⟨hgoodIn, hnearIn⟩
      apply hgoodVerify.mpr
      refine ⟨?_, hnearRepB.mpr hnearIn⟩
      rw [hgoodValue₁]
      exact hgoodIn
  refine ⟨σ₂, current', labelA, repClass', repsA', nextA', repA', S,
    ?_, hAdata, hApartition, ?_, hnextBCount₂, hcount₂, hactiveA₂, hactiveB₂,
    hrepsA₂, hrepsB₂, hnextA₂, hnextB₂, hrepA₂, hrepB₂, hgoodExact⟩
  · simpa [secondPartitionAndVerify, seqs] using rpartition.seq rverify
  · intro hgood v hv
    exact hnearRepB.mp (hnearVerify hgood) v hv

/-- Backwards-compatible projection retaining the original successful-check
contract. -/
lemma secondPartitionAndVerify_run
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
    (hnextBArray : σ.arrs "nextB" = arrOf n nextB)
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
              (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound) ∧
      σ'.vars "nextBCount" = R.card ∧
      σ'.vars "nextACount" = S.card ∧
      σ'.arrs "activeA" = arrOf n activeA ∧
      σ'.arrs "activeB" = arrOf n activeB ∧
      σ'.arrs "repsA" = arrOf n repsA' ∧
      σ'.arrs "repsB" = arrOf n repsB ∧
      σ'.arrs "nextA" = arrOf n nextA' ∧
      σ'.arrs "nextB" = arrOf n nextB ∧
      σ'.arrs "repA" = arrOf n repA' ∧
      σ'.arrs "repB" = arrOf n repB := by
  obtain ⟨σ', current', labelA, repClass', repsA', nextA', repA', S,
      hrun, hdata, hpartition, hnear, hnextBCount', hnextACount',
      hactiveA', hactiveB', hrepsA', hrepsB', hnextA', hnextB',
      hrepA', hrepB', _⟩ := secondPartitionAndVerify_run_full
    hx htargetCap hn hnextBCount hbound hgoodB hoff htarget hactiveAArray
    hactiveBArray hrepsB hnextBArray hrepB hclassA hclassSize hmarkedCount
    hstamp hmarked htouched hsplit hrepClass hrepsA hnextA hrepA hdegree
    hinter hneighbors hBdata hBpartition hactiveANonempty hactiveAB
    hactiveBB hnB htargetCapB hboundB
  exact ⟨σ', current', labelA, repClass', repsA', nextA', repA', S,
    hrun, hdata, hpartition, hnear, hnextBCount', hnextACount', hactiveA',
    hactiveB', hrepsA', hrepsB', hnextA', hnextB', hrepA', hrepB'⟩

end

end Lax235315Proofs.Construction.RoundVerifySource
