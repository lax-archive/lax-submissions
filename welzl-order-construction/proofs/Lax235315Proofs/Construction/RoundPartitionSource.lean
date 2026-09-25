import Lax235315Proofs.Construction.PartitionCompleteSource
import Mathlib.Tactic

/-! Concrete specialization of the trace-partition verifier to the first
partition call in a reduction round. -/

namespace Lax235315Proofs.Construction.RoundPartitionSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PartitionCompleteSource
open Lax235315Proofs.Construction.PartitionLoopSource
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlStraight

noncomputable section

theorem testPrefix_eq_finSetAsSet_of_prefixEnumerates
    {n count : ℕ} {tests : ℕ → ℕ} {W : Finset ℕ}
    (henum : PrefixEnumerates count tests W) :
    testPrefix (n := n) tests count = finSetAsSet W := by
  ext v
  change (∃ j < count, tests j = v.val) ↔ v.val ∈ W
  rw [← henum.2]
  simp [Stack.toList, arrOf]

theorem PrefixEnumerates.entry_lt
    {n count : ℕ} {tests : ℕ → ℕ} {W : Finset ℕ}
    (henum : PrefixEnumerates count tests W)
    (hWrange : ∀ v ∈ W, v < n) :
    ∀ i < count, tests i < n := by
  intro i hi
  apply hWrange (tests i)
  apply (henum.2 (tests i)).mp
  simp only [Stack.toList, arrOf, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

/-- The first concrete partition call of a reduction round partitions the
active `B` side by the sampled prefix of the random order. -/
theorem firstPartition_run
    {B n targetCap sampleCount : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {activeB ord classB classSize markedCount stamp marked
      touched split repClass repsB nextB repB : ℕ → ℕ}
    {W : Finset ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n)
    (hsampleCount : σ.vars "sampleCount" = sampleCount)
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
    (henum : PrefixEnumerates sampleCount ord W)
    (hWrange : ∀ v ∈ W, v < n)
    (hactiveNonempty : (activeVertices n activeB).Nonempty)
    (hsampleCountN : sampleCount ≤ n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, activeB v < B) :
    ∃ σ' current label repClass' repsB' nextB' repB' R,
      Run B (partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount") σ σ'
        (partitionCost x ord n sampleCount) ∧
      σ'.vars "nextBCount" = R.card ∧
      σ'.arrs "activeB" = arrOf n activeB ∧
      σ'.arrs "classB" = arrOf n label ∧
      σ'.arrs "repClass" = arrOf n repClass' ∧
      σ'.arrs "repsB" = arrOf n repsB' ∧
      σ'.arrs "nextB" = arrOf n nextB' ∧
      σ'.arrs "repB" = arrOf n repB' ∧
      RepData n current n activeB label repClass' repsB' nextB' R ∧
      (∀ v < n, activeB v = 1 → repB' v = repClass' (label v)) ∧
      Nonempty (ConcreteTracePartition G activeB (finSetAsSet W) R repB') := by
  have htestsRange := PrefixEnumerates.entry_lt henum hWrange
  obtain ⟨σ', current, label, repClass', repsB', nextB', repB', R,
      rpartition, hnextBCount, hactiveB', hclassB', hrepClass', hrepsB',
      hnextB', hrepB', hdata, hmap, htrace⟩ :=
    PartitionCompleteSource.partition_run
      (activeName := "activeB") (testsName := "ord")
      (testCountName := "sampleCount") (clsName := "classB")
      (repsName := "repsB") (activeOutName := "nextB")
      (repOfName := "repB") (outCountName := "nextBCount")
      hx htargetCap hn hsampleCount hoff
      htarget hactiveBArray hord hclassB hclassSize hmarkedCount hstamp
      hmarked htouched hsplit hrepClass hrepsB hnextB hrepB hactiveNonempty
      hsampleCountN htestsRange hnB htargetCapB honeB hactiveB
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ', current, label, repClass', repsB', nextB', repB', R,
    rpartition, hnextBCount, hactiveB', hclassB', hrepClass', hrepsB',
    hnextB', hrepB', hdata, hmap, ?_⟩
  simpa [testPrefix_eq_finSetAsSet_of_prefixEnumerates henum] using htrace

/-- The second concrete partition call uses the representatives selected by
the first call as its duplicate-free test prefix, and partitions the active
`A` side by their neighborhood traces. -/
theorem secondPartition_run
    {B n targetCap current : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {activeA activeB labelB repClassB repsB nextB
      classA classSize markedCount stamp marked touched split
      oldRepClass repsA nextA repA : ℕ → ℕ}
    {R : Finset ℕ} {σ : Env}
    (hx : EncodesGraph x n G) (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n)
    (hnextBCount : σ.vars "nextBCount" = R.card)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactiveAArray : σ.arrs "activeA" = arrOf n activeA)
    (hrepsB : σ.arrs "repsB" = arrOf n repsB)
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
    (hBdata : RepData n current n activeB labelB repClassB repsB nextB R)
    (hactiveANonempty : (activeVertices n activeA).Nonempty)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hactiveAB : ∀ v < n, activeA v < B) :
    ∃ σ' current' labelA repClass' repsA' nextA' repA' S,
      Run B (partition "activeA" "repsB" "nextBCount" "classA"
        "repsA" "nextA" "repA" "nextACount") σ σ'
        (partitionCost x repsB n R.card) ∧
      σ'.vars "nextACount" = S.card ∧
      σ'.arrs "activeA" = arrOf n activeA ∧
      σ'.arrs "classA" = arrOf n labelA ∧
      σ'.arrs "repClass" = arrOf n repClass' ∧
      σ'.arrs "repsA" = arrOf n repsA' ∧
      σ'.arrs "nextA" = arrOf n nextA' ∧
      σ'.arrs "repA" = arrOf n repA' ∧
      RepData n current' n activeA labelA repClass' repsA' nextA' S ∧
      (∀ v < n, activeA v = 1 → repA' v = repClass' (labelA v)) ∧
      Nonempty (ConcreteTracePartition G activeA (finSetAsSet R) S repA') := by
  have hRrange : ∀ v ∈ R, v < n := by
    intro v hv
    exact (mem_activeVertices.mp (hBdata.reps_processed hv)).1
  have hRcardN : R.card ≤ n := by
    calc
      R.card ≤ (Finset.range n).card := Finset.card_le_card (by
        intro v hv
        exact Finset.mem_range.mpr (hRrange v hv))
      _ = n := Finset.card_range n
  have htestsRange := PrefixEnumerates.entry_lt hBdata.enum hRrange
  obtain ⟨σ', current', labelA, repClass', repsA', nextA', repA', S,
      rpartition, hnextACount, hactiveA', hclassA', hrepClass', hrepsA',
      hnextA', hrepA', hdata, hmap, htrace⟩ :=
    PartitionCompleteSource.partition_run
      (activeName := "activeA") (testsName := "repsB")
      (testCountName := "nextBCount") (clsName := "classA")
      (repsName := "repsA") (activeOutName := "nextA")
      (repOfName := "repA") (outCountName := "nextACount")
      hx htargetCap hn hnextBCount hoff htarget hactiveAArray hrepsB hclassA
      hclassSize hmarkedCount hstamp hmarked htouched hsplit hrepClass hrepsA
      hnextA hrepA hactiveANonempty hRcardN htestsRange hnB htargetCapB honeB
      hactiveAB
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ', current', labelA, repClass', repsA', nextA', repA', S,
    rpartition, hnextACount, hactiveA', hclassA', hrepClass', hrepsA',
    hnextA', hrepA', hdata, hmap, ?_⟩
  simpa [testPrefix_eq_finSetAsSet_of_prefixEnumerates hBdata.enum] using htrace

end

end Lax235315Proofs.Construction.RoundPartitionSource
