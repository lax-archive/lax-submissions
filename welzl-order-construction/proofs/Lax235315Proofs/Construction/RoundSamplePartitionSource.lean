import Lax235315Proofs.Construction.RoundPartitionSource
import Lax235315Proofs.Construction.RoundVerifySource
import Lax235315Proofs.Construction.SampleCountSource
import Lax235315Proofs.Construction.Sampling
import Mathlib.Tactic

/-! Source-level composition of the sample-size calculation and the first
trace partition in a reduction round. -/

namespace Lax235315Proofs.Construction.RoundSamplePartitionSource

open scoped symmDiff
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.PartitionCompleteSource
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.RoundPartitionSource
open Lax235315Proofs.Construction.RoundVerifySource
open Lax235315Proofs.Construction.SampleCountSource
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.WelzlProgram

noncomputable section

/-- Every finite numeric vertex set has a duplicate-free `Fin n` listing. -/
theorem exists_enumerates_finSetAsSet {n : ℕ} (S : Finset ℕ) :
    ∃ small : List (Fin n), Enumerates (finSetAsSet S) small := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun v => v.val ∈ S
  refine ⟨T.toList, T.nodup_toList, ?_⟩
  intro v
  simp [T, finSetAsSet]

/-- The deterministic prefix of an accepted reduction branch, through its
first trace partition. -/
def prepareAndFirstPartition : Com :=
  seqs [
    prepareSampleCount,
    partition "activeB" "ord" "sampleCount" "classB"
      "repsB" "nextB" "repB" "nextBCount"]

/-- The whole deterministic certificate-building part of a collision-free
round, stopping just before the success branch is committed. -/
def preparePartitionsAndVerify : Com :=
  buildReductionCertificate

/-- Computing the prescribed sample size and then executing the first
partition produces a concrete partition by exactly that sampled prefix. -/
theorem prepareAndFirstPartition_run
    {B n targetCap a c : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {activeB ord classB classSize markedCount stamp marked
      touched split repClass repsB nextB repB : ℕ → ℕ}
    {W : Finset ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n) (hacount : σ.vars "acount" = a)
    (hcsq : σ.vars "csq" = c ^ 2)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactiveBArray : σ.arrs "activeB" = arrOf n activeB)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hclassB : σ.arrs "classB" = arrOf n classB)
    (hclassSize : σ.arrs "classSize" = arrOf n classSize)
    (hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hsplit : σ.arrs "split" = arrOf n split)
    (hrepClass : σ.arrs "repClass" = arrOf n repClass)
    (hrepsB : σ.arrs "repsB" = arrOf n repsB)
    (hnextB : σ.arrs "nextB" = arrOf n nextB)
    (hrepB : σ.arrs "repB" = arrOf n repB)
    (henum : PrefixEnumerates (sampleSize a c) ord W)
    (hWrange : ∀ v ∈ W, v < n)
    (hactiveNonempty : (activeVertices n activeB).Nonempty)
    (hc : 1 ≤ c) (ha : 0 < a) (haN : a ≤ n)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (hdenomB : 2 * c ^ 2 < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, activeB v < B) :
    ∃ σ' current label repClass' repsB' nextB' repB' R,
      Run B prepareAndFirstPartition σ σ'
        (22 + partitionCost x ord n (sampleSize a c)) ∧
      σ'.vars "nextBCount" = R.card ∧
      σ'.arrs "activeB" = arrOf n activeB ∧
      σ'.arrs "classB" = arrOf n label ∧
      σ'.arrs "repClass" = arrOf n repClass' ∧
      σ'.arrs "repsB" = arrOf n repsB' ∧
      σ'.arrs "nextB" = arrOf n nextB' ∧
      σ'.arrs "repB" = arrOf n repB' ∧
      RepData n current n activeB label repClass' repsB' nextB' R ∧
      Nonempty (ConcreteTracePartition G activeB (finSetAsSet W) R repB') := by
  have haB : a < B := haN.trans_lt hnB
  obtain ⟨σ₁, rprepare, hdenom₁, hsample₁⟩ :=
    prepareSampleCount_run hacount hcsq hc ha haB hdenomB
  have hn₁ : σ₁.vars "n" = n := by
    rw [rprepare.frame_var "n" (by native_decide), hn]
  have hoff₁ : σ₁.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [rprepare.frame_arr "off" (by native_decide), hoff]
  have htarget₁ : σ₁.arrs "tgt" = arrOf targetCap (target x) := by
    rw [rprepare.frame_arr "tgt" (by native_decide), htarget]
  have hactiveB₁ : σ₁.arrs "activeB" = arrOf n activeB := by
    rw [rprepare.frame_arr "activeB" (by native_decide), hactiveBArray]
  have hord₁ : σ₁.arrs "ord" = arrOf n ord := by
    rw [rprepare.frame_arr "ord" (by native_decide), hord]
  have hclassB₁ : σ₁.arrs "classB" = arrOf n classB := by
    rw [rprepare.frame_arr "classB" (by native_decide), hclassB]
  have hclassSize₁ : σ₁.arrs "classSize" = arrOf n classSize := by
    rw [rprepare.frame_arr "classSize" (by native_decide), hclassSize]
  have hmarkedCount₁ : σ₁.arrs "markedCount" = arrOf n markedCount := by
    rw [rprepare.frame_arr "markedCount" (by native_decide), hmarkedCount]
  have hstamp₁ : σ₁.arrs "stamp" = arrOf n stamp := by
    rw [rprepare.frame_arr "stamp" (by native_decide), hstamp]
  have hmarked₁ : σ₁.arrs "marked" = arrOf n marked := by
    rw [rprepare.frame_arr "marked" (by native_decide), hmarked]
  have htouched₁ : σ₁.arrs "touched" = arrOf n touched := by
    rw [rprepare.frame_arr "touched" (by native_decide), htouched]
  have hsplit₁ : σ₁.arrs "split" = arrOf n split := by
    rw [rprepare.frame_arr "split" (by native_decide), hsplit]
  have hrepClass₁ : σ₁.arrs "repClass" = arrOf n repClass := by
    rw [rprepare.frame_arr "repClass" (by native_decide), hrepClass]
  have hrepsB₁ : σ₁.arrs "repsB" = arrOf n repsB := by
    rw [rprepare.frame_arr "repsB" (by native_decide), hrepsB]
  have hnextB₁ : σ₁.arrs "nextB" = arrOf n nextB := by
    rw [rprepare.frame_arr "nextB" (by native_decide), hnextB]
  have hrepB₁ : σ₁.arrs "repB" = arrOf n repB := by
    rw [rprepare.frame_arr "repB" (by native_decide), hrepB]
  obtain ⟨σ₂, current, label, repClass', repsB', nextB', repB', R,
      rpartition, hnextBCount, hactiveB₂, hclassB₂, hrepClass₂,
      hrepsB₂, hnextB₂, hrepB₂, hdata, -, hpartition⟩ :=
    firstPartition_run hx htargetCap hn₁ hsample₁ hoff₁ htarget₁
      hactiveB₁ hord₁ hclassB₁ hclassSize₁ hmarkedCount₁ hstamp₁ hmarked₁
      htouched₁ hsplit₁ hrepClass₁ hrepsB₁ hnextB₁ hrepB₁ henum hWrange
      hactiveNonempty ((sampleSize_le_self hc ha).trans haN) hnB htargetCapB
      honeB hactiveB
  refine ⟨σ₂, current, label, repClass', repsB', nextB', repB', R,
    ?_, hnextBCount, hactiveB₂, hclassB₂, hrepClass₂, hrepsB₂,
    hnextB₂, hrepB₂, hdata, hpartition⟩
  simpa [prepareAndFirstPartition, seqs] using rprepare.seq rpartition

/-- From a sampled prefix, the literal collision-free round suffix builds
both concrete trace partitions and checks the near-twin condition required
for an abstract reduction. -/
theorem preparePartitionsAndVerify_run
    {B n targetCap a c bound : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ}
    {activeA activeB ord classB classA classSize markedCount stamp marked
      touched split repClass repsB nextB repB repsA nextA repA degree inter
      neighbors : ℕ → ℕ}
    {W : Finset ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n) (hacount : σ.vars "acount" = a)
    (hcsq : σ.vars "csq" = c ^ 2)
    (hbound : σ.vars "nearBound" = bound) (hgoodB : σ.vars "good" < B)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactiveAArray : σ.arrs "activeA" = arrOf n activeA)
    (hactiveBArray : σ.arrs "activeB" = arrOf n activeB)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hclassB : σ.arrs "classB" = arrOf n classB)
    (hclassA : σ.arrs "classA" = arrOf n classA)
    (hclassSize : σ.arrs "classSize" = arrOf n classSize)
    (hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hsplit : σ.arrs "split" = arrOf n split)
    (hrepClass : σ.arrs "repClass" = arrOf n repClass)
    (hrepsB : σ.arrs "repsB" = arrOf n repsB)
    (hnextB : σ.arrs "nextB" = arrOf n nextB)
    (hrepB : σ.arrs "repB" = arrOf n repB)
    (hrepsA : σ.arrs "repsA" = arrOf n repsA)
    (hnextA : σ.arrs "nextA" = arrOf n nextA)
    (hrepA : σ.arrs "repA" = arrOf n repA)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hneighbors : σ.arrs "neighbors" = arrOf n neighbors)
    (henum : PrefixEnumerates (sampleSize a c) ord W)
    (hWrange : ∀ v ∈ W, v < n)
    (hactiveANonempty : (activeVertices n activeA).Nonempty)
    (hactiveBNonempty : (activeVertices n activeB).Nonempty)
    (hc : 1 ≤ c) (ha : 0 < a) (haN : a ≤ n)
    (hactiveAB : ∀ v < n, activeA v < B)
    (hactiveBB : ∀ v < n, activeB v < B)
    (hnB : 2 * n + 1 < B) (htargetCapB : targetCap < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ' currentB labelB' repClassB' repsB' nextB' repB' R,
      ∃ hBpartition : ConcreteTracePartition G activeB (finSetAsSet W) R repB',
      ∃ current' labelA' repClassA' repsA' nextA' repA' S,
      Run B preparePartitionsAndVerify σ σ'
        (22 + partitionCost x ord n (sampleSize a c) +
          (partitionCost x repsB' n R.card + 400 * (n + targetCap + 1))) ∧
      RepData n currentB n activeB labelB' repClassB' repsB' nextB' R ∧
      RepData n current' n activeA labelA' repClassA' repsA' nextA' S ∧
      Nonempty (ConcreteTracePartition G activeA (finSetAsSet R) S repA') ∧
      (σ'.vars "good" = 1 →
        ∀ (v : Fin n) (hv : activeB v.val = 1),
          ((G.neighborSet v ∩
              (activeFinset (n := n) activeA : Set (Fin n))) ∆
            (G.neighborSet (hBpartition.partition.representative v) ∩
              (activeFinset (n := n) activeA : Set (Fin n)))).ncard ≤ bound) ∧
      (σ'.vars "good" = 1 →
        ∃ small big : List (Fin n),
          Enumerates (finSetAsSet S) small ∧
          Nonempty (Reduction G bound
            {v : Fin n | activeA v.val = 1}
            {v : Fin n | activeB v.val = 1}
            (finSetAsSet S) (finSetAsSet R) small big)) := by
  obtain ⟨σ₁, currentB, labelB', repClassB', repsB', nextB', repB', R,
      rfirst, hnextBCount, hactiveB₁, -, hrepClass₁, hrepsB₁, -, hrepB₁,
      hBdata, hBnonempty⟩ :=
    prepareAndFirstPartition_run hx htargetCap hn hacount hcsq hoff htarget
      hactiveBArray hord hclassB hclassSize hmarkedCount hstamp hmarked
      htouched hsplit hrepClass hrepsB hnextB hrepB henum hWrange
      hactiveBNonempty hc ha haN (by omega) htargetCapB hdenomB (by omega)
      hactiveBB
  obtain ⟨hBpartition⟩ := hBnonempty
  have hn₁ : σ₁.vars "n" = n := by
    rw [rfirst.frame_var "n" (by native_decide), hn]
  have hbound₁ : σ₁.vars "nearBound" = bound := by
    rw [rfirst.frame_var "nearBound" (by native_decide), hbound]
  have hgoodB₁ : σ₁.vars "good" < B := by
    rw [rfirst.frame_var "good" (by native_decide)]
    exact hgoodB
  have hoff₁ : σ₁.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [rfirst.frame_arr "off" (by native_decide), hoff]
  have htarget₁ : σ₁.arrs "tgt" = arrOf targetCap (target x) := by
    rw [rfirst.frame_arr "tgt" (by native_decide), htarget]
  have hactiveA₁ : σ₁.arrs "activeA" = arrOf n activeA := by
    rw [rfirst.frame_arr "activeA" (by native_decide), hactiveAArray]
  have hclassA₁ : σ₁.arrs "classA" = arrOf n classA := by
    rw [rfirst.frame_arr "classA" (by native_decide), hclassA]
  have hrepsA₁ : σ₁.arrs "repsA" = arrOf n repsA := by
    rw [rfirst.frame_arr "repsA" (by native_decide), hrepsA]
  have hnextA₁ : σ₁.arrs "nextA" = arrOf n nextA := by
    rw [rfirst.frame_arr "nextA" (by native_decide), hnextA]
  have hrepA₁ : σ₁.arrs "repA" = arrOf n repA := by
    rw [rfirst.frame_arr "repA" (by native_decide), hrepA]
  have hdegree₁ : σ₁.arrs "degree" = arrOf n degree := by
    rw [rfirst.frame_arr "degree" (by native_decide), hdegree]
  have hinter₁ : σ₁.arrs "inter" = arrOf n inter := by
    rw [rfirst.frame_arr "inter" (by native_decide), hinter]
  have hneighbors₁ : σ₁.arrs "neighbors" = arrOf n neighbors := by
    rw [rfirst.frame_arr "neighbors" (by native_decide), hneighbors]
  have hclassSizeLen : (σ₁.arrs "classSize").length = n := by
    rw [run_array_length_eq rfirst "classSize", hclassSize, length_arrOf]
  have hmarkedCountLen : (σ₁.arrs "markedCount").length = n := by
    rw [run_array_length_eq rfirst "markedCount", hmarkedCount, length_arrOf]
  have hstampLen : (σ₁.arrs "stamp").length = n := by
    rw [run_array_length_eq rfirst "stamp", hstamp, length_arrOf]
  have hmarkedLen : (σ₁.arrs "marked").length = n := by
    rw [run_array_length_eq rfirst "marked", hmarked, length_arrOf]
  have htouchedLen : (σ₁.arrs "touched").length = n := by
    rw [run_array_length_eq rfirst "touched", htouched, length_arrOf]
  have hsplitLen : (σ₁.arrs "split").length = n := by
    rw [run_array_length_eq rfirst "split", hsplit, length_arrOf]
  obtain ⟨classSize₁, hclassSize₁⟩ := exists_arrOf_of_length hclassSizeLen
  obtain ⟨markedCount₁, hmarkedCount₁⟩ := exists_arrOf_of_length hmarkedCountLen
  obtain ⟨stamp₁, hstamp₁⟩ := exists_arrOf_of_length hstampLen
  obtain ⟨marked₁, hmarked₁⟩ := exists_arrOf_of_length hmarkedLen
  obtain ⟨touched₁, htouched₁⟩ := exists_arrOf_of_length htouchedLen
  obtain ⟨split₁, hsplit₁⟩ := exists_arrOf_of_length hsplitLen
  obtain ⟨σ₂, current', labelA', repClassA', repsA', nextA', repA', S,
      rsecond, hAdata, hApartition, hnear⟩ :=
    secondPartitionAndVerify_run hx htargetCap hn₁ hnextBCount hbound₁ hgoodB₁
      hoff₁ htarget₁ hactiveA₁ hactiveB₁ hrepsB₁ hrepB₁ hclassA₁
      hclassSize₁ hmarkedCount₁ hstamp₁ hmarked₁ htouched₁ hsplit₁
      hrepClass₁ hrepsA₁ hnextA₁ hrepA₁ hdegree₁ hinter₁ hneighbors₁
      hBdata hBpartition hactiveANonempty hactiveAB hactiveBB hnB
      htargetCapB hboundB
  refine ⟨σ₂, currentB, labelB', repClassB', repsB', nextB', repB', R,
    hBpartition,
    current', labelA', repClassA', repsA', nextA', repA', S, ?_, hBdata,
    hAdata, hApartition, ?_, ?_⟩
  · simpa [preparePartitionsAndVerify, buildReductionCertificate,
      prepareAndFirstPartition, secondPartitionAndVerify, seqs, Nat.add_assoc] using
      rfirst.seq rsecond
  · simpa only using hnear
  · intro hgood
    obtain ⟨hAconcrete⟩ := hApartition
    obtain ⟨small, hsmall⟩ := exists_enumerates_finSetAsSet S
    have hnear' := hnear hgood
    have hnearSet : ∀ b ∈ ({v : Fin n | activeB v.val = 1} : Set (Fin n)),
        ((G.neighborSet b ∩ {v : Fin n | activeA v.val = 1}) ∆
          (G.neighborSet (hBpartition.partition.representative b) ∩
            {v : Fin n | activeA v.val = 1})).ncard ≤ bound := by
      intro b hb
      simpa [activeFinset] using hnear' b hb
    obtain ⟨big, hred⟩ := exists_reduction_of_concrete_partitions
      hBpartition hAconcrete hnearSet hsmall
    exact ⟨small, big, hsmall, hred⟩

end

end Lax235315Proofs.Construction.RoundSamplePartitionSource
