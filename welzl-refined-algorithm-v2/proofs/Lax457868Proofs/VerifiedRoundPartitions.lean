import Lax457868Proofs.VerifiedPartitionBridge
import Lax457868Proofs.RefinedContraction
import Lax235315Proofs.Construction.RoundPartitionSource
import Lax808846Proofs.Frame

set_option autoImplicit false

/-! Execute the two unchanged concrete partition commands in sequence. -/

namespace Lax457868Proofs.VerifiedRoundPartitions

open Lax457868Proofs.ContractionRounds
open Lax457868Proofs.VerifiedPartitionBridge
open Lax457868Proofs.RefinedContraction
open Lax457868Proofs.RefinedSampleSpec
open Lax457868Proofs.SamplerContract
open Lax195003.WelzlOrdersNeighborhoodComplexity
open Lax457868Proofs.GraphTraceBounds
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.PartitionCompleteSource
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.RoundPartitionSource
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.WelzlProgram
open Lax808846Proofs.Imp
open Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding

noncomputable section

/-- Initial arrays and invariants for the two unchanged source commands.
`henum` certifies that the sample prefix is duplicate-free and enumerates
`Wnum`. -/
structure RoundPartitionInput (B n targetCap sampleCount : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ)
    (A Bset : Finset (Fin n)) (Wnum : Finset ℕ) where
  σ : Env
  activeA : ℕ → ℕ
  activeB : ℕ → ℕ
  ord : ℕ → ℕ
  classA : ℕ → ℕ
  classB : ℕ → ℕ
  classSize : ℕ → ℕ
  markedCount : ℕ → ℕ
  stamp : ℕ → ℕ
  marked : ℕ → ℕ
  touched : ℕ → ℕ
  split : ℕ → ℕ
  repClass : ℕ → ℕ
  repsA : ℕ → ℕ
  repsB : ℕ → ℕ
  nextA : ℕ → ℕ
  nextB : ℕ → ℕ
  repA : ℕ → ℕ
  repB : ℕ → ℕ
  hx : EncodesGraph x n G
  htargetCap : targetCap = 2 * edgeCount x
  hn : σ.vars "n" = n
  hsampleCount : σ.vars "sampleCount" = sampleCount
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htarget : σ.arrs "tgt" = arrOf targetCap (target x)
  hactiveAArray : σ.arrs "activeA" = arrOf n activeA
  hactiveBArray : σ.arrs "activeB" = arrOf n activeB
  hord : σ.arrs "ord" = arrOf n ord
  hclassA : σ.arrs "classA" = arrOf n classA
  hclassB : σ.arrs "classB" = arrOf n classB
  hclassSize : σ.arrs "classSize" = arrOf n classSize
  hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount
  hstamp : σ.arrs "stamp" = arrOf n stamp
  hmarked : σ.arrs "marked" = arrOf n marked
  htouched : σ.arrs "touched" = arrOf n touched
  hsplit : σ.arrs "split" = arrOf n split
  hrepClass : σ.arrs "repClass" = arrOf n repClass
  hrepsA : σ.arrs "repsA" = arrOf n repsA
  hrepsB : σ.arrs "repsB" = arrOf n repsB
  hnextA : σ.arrs "nextA" = arrOf n nextA
  hnextB : σ.arrs "nextB" = arrOf n nextB
  hrepA : σ.arrs "repA" = arrOf n repA
  hrepB : σ.arrs "repB" = arrOf n repB
  henum : PrefixEnumerates sampleCount ord Wnum
  hWrange : ∀ v ∈ Wnum, v < n
  hactiveANonempty : (activeVertices n activeA).Nonempty
  hactiveBNonempty : (activeVertices n activeB).Nonempty
  hsampleCountN : sampleCount ≤ n
  hnB : n < B
  htargetCapB : targetCap < B
  honeB : 1 < B
  hactiveABound : ∀ v < n, activeA v < B
  hactiveBBound : ∀ v < n, activeB v < B
  hAactive : ∀ v : Fin n, v ∈ A ↔ activeA v.val = 1
  hBactive : ∀ v : Fin n, v ∈ Bset ↔ activeB v.val = 1
  hWsubsetA : finsetOfNumeric Wnum ⊆ A

private lemma run_array_length {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hbs⟩ := h
  induction hbs with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih₁ ih₂ =>
      rw [ih₂ (by omega), ih₁ (by omega)]
  | ite_true _ _ ih => exact ih (by omega)
  | ite_false _ _ ih => exact ih (by omega)
  | while_true _ _ _ ihbody ihloop =>
      rw [ihloop (by omega), ihbody (by omega)]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

private lemma arr_eq_arrOf_getD (a : List ℕ) (n : ℕ)
    (hlen : a.length = n) :
    a = arrOf n (fun i => a.getD i 0) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi _
    simp only [arrOf, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl

private def reindexPartition {n : ℕ} {G : SimpleGraph (Fin n)}
    {V S R V' S' R' : Set (Fin n)}
    (h : TracePartition G V S R) (hV : V' = V) (hS : S' = S)
    (hR : R' = R) : TracePartition G V' S' R' := hV ▸ hS ▸ hR ▸ h

/-- Run the first source command on the prefix, then the second on the exact
representative list and count written by the first. All arrays the second
command does not write are preserved using the source `Run.frame_arr` rule. -/
lemma runVerifiedRoundPartitions {B n targetCap sampleCount : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A Bset : Finset (Fin n)} {Wnum : Finset ℕ}
    (I : RoundPartitionInput B n targetCap sampleCount G x A Bset Wnum) :
    ∃ σ₁ σ₂ : Env, ∃ currentB currentA : ℕ, ∃ R S : Finset ℕ,
      ∃ labelB repClassB repsB' nextB' repB' labelA repClassA repsA' nextA' repA' :
        ℕ → ℕ,
      ∃ _hB : ConcreteTracePartition G I.activeB (finSetAsSet Wnum) R repB',
      ∃ _hA : ConcreteTracePartition G I.activeA (finSetAsSet R) S repA',
      Run B (partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount") I.σ σ₁
          (partitionCost x I.ord n sampleCount) ∧
      Run B (partition "activeA" "repsB" "nextBCount" "classA"
        "repsA" "nextA" "repA" "nextACount") σ₁ σ₂
          (partitionCost x repsB' n R.card) ∧
      Run B (Com.seq
        (partition "activeB" "ord" "sampleCount" "classB"
          "repsB" "nextB" "repB" "nextBCount")
        (partition "activeA" "repsB" "nextBCount" "classA"
          "repsA" "nextA" "repA" "nextACount")) I.σ σ₂
          (partitionCost x I.ord n sampleCount + partitionCost x repsB' n R.card) ∧
      RepData n currentB n I.activeB labelB repClassB repsB' nextB' R ∧
      RepData n currentA n I.activeA labelA repClassA repsA' nextA' S ∧
      σ₁.vars "nextBCount" = R.card ∧ σ₂.vars "nextACount" = S.card ∧
      σ₂.vars "nextBCount" = R.card ∧
      σ₂.arrs "activeB" = arrOf n I.activeB ∧
      σ₂.arrs "repsB" = arrOf n repsB' ∧ σ₂.arrs "repB" = arrOf n repB' ∧
      σ₂.arrs "nextB" = arrOf n nextB' ∧
      σ₂.arrs "activeA" = arrOf n I.activeA ∧
      σ₂.arrs "repsA" = arrOf n repsA' ∧ σ₂.arrs "repA" = arrOf n repA' ∧
      σ₂.arrs "nextA" = arrOf n nextA' ∧
      ∃ contraction : TraceContraction A Bset (finiteNeighborhood G A)
          (finsetOfNumeric Wnum),
        (∀ b ∈ Bset, (contraction.bChoice.representative b).val = repB' b.val) ∧
        (∀ a ∈ A, (contraction.aChoice.representative a).val = repA' a.val) ∧
        contraction.retainedB = finsetOfNumeric R ∧
        contraction.retainedA = finsetOfNumeric S ∧
        partitionCost x I.ord n sampleCount + partitionCost x repsB' n R.card ≤
          1800 * (x.length + 1) := by
  classical
  obtain ⟨σ₁, currentB, labelB, repClassB, repsB', nextB', repB', R,
    runB, hnextBCount, hactiveB', hclassB', hrepClassB', hrepsB',
    hnextB', hrepB', dataB, hmapB, certB⟩ :=
    Lax235315Proofs.Construction.RoundPartitionSource.firstPartition_run
      I.hx I.htargetCap I.hn I.hsampleCount I.hoff I.htarget
      I.hactiveBArray I.hord I.hclassB I.hclassSize I.hmarkedCount
      I.hstamp I.hmarked I.htouched I.hsplit I.hrepClass I.hrepsB
      I.hnextB I.hrepB I.henum I.hWrange I.hactiveBNonempty
      I.hsampleCountN I.hnB I.htargetCapB I.honeB I.hactiveBBound
  have hactiveA₁ : σ₁.arrs "activeA" = arrOf n I.activeA :=
    (runB.frame_arr "activeA" (by decide)).trans I.hactiveAArray
  have hclassA₁ : σ₁.arrs "classA" = arrOf n I.classA :=
    (runB.frame_arr "classA" (by decide)).trans I.hclassA
  let classSize₁ := fun i => (σ₁.arrs "classSize").getD i 0
  have hclassSize₁ : σ₁.arrs "classSize" = arrOf n classSize₁ := by
    exact arr_eq_arrOf_getD _ n (by
      rw [run_array_length runB, I.hclassSize, length_arrOf])
  let markedCount₁ := fun i => (σ₁.arrs "markedCount").getD i 0
  have hmarkedCount₁ : σ₁.arrs "markedCount" = arrOf n markedCount₁ := by
    exact arr_eq_arrOf_getD _ n (by
      rw [run_array_length runB, I.hmarkedCount, length_arrOf])
  let stamp₁ := fun i => (σ₁.arrs "stamp").getD i 0
  have hstamp₁ : σ₁.arrs "stamp" = arrOf n stamp₁ := by
    exact arr_eq_arrOf_getD _ n (by
      rw [run_array_length runB, I.hstamp, length_arrOf])
  let marked₁ := fun i => (σ₁.arrs "marked").getD i 0
  have hmarked₁ : σ₁.arrs "marked" = arrOf n marked₁ := by
    exact arr_eq_arrOf_getD _ n (by
      rw [run_array_length runB, I.hmarked, length_arrOf])
  let touched₁ := fun i => (σ₁.arrs "touched").getD i 0
  have htouched₁ : σ₁.arrs "touched" = arrOf n touched₁ := by
    exact arr_eq_arrOf_getD _ n (by
      rw [run_array_length runB, I.htouched, length_arrOf])
  let split₁ := fun i => (σ₁.arrs "split").getD i 0
  have hsplit₁ : σ₁.arrs "split" = arrOf n split₁ := by
    exact arr_eq_arrOf_getD _ n (by
      rw [run_array_length runB, I.hsplit, length_arrOf])
  have hrepsA₁ : σ₁.arrs "repsA" = arrOf n I.repsA :=
    (runB.frame_arr "repsA" (by decide)).trans I.hrepsA
  have hnextA₁ : σ₁.arrs "nextA" = arrOf n I.nextA :=
    (runB.frame_arr "nextA" (by decide)).trans I.hnextA
  have hrepA₁ : σ₁.arrs "repA" = arrOf n I.repA :=
    (runB.frame_arr "repA" (by decide)).trans I.hrepA
  have hn₁ : σ₁.vars "n" = n :=
    (runB.frame_var "n" (by decide)).trans I.hn
  have hoff₁ : σ₁.arrs "off" = arrOf (n + 1) (offset x) :=
    (runB.frame_arr "off" (by decide)).trans I.hoff
  have htarget₁ : σ₁.arrs "tgt" = arrOf targetCap (target x) :=
    (runB.frame_arr "tgt" (by decide)).trans I.htarget
  obtain ⟨σ₂, currentA, labelA, repClassA, repsA', nextA', repA', S,
    runA, hnextACount, hactiveA', hclassA', hrepClassA', hrepsA',
    hnextA', hrepA', dataA, hmapA, certA⟩ :=
    Lax235315Proofs.Construction.RoundPartitionSource.secondPartition_run
      I.hx I.htargetCap hn₁ hnextBCount hoff₁ htarget₁ hactiveA₁
      hrepsB' hclassA₁ hclassSize₁ hmarkedCount₁ hstamp₁ hmarked₁
      htouched₁ hsplit₁ hrepClassB' hrepsA₁ hnextA₁ hrepA₁ dataB
      I.hactiveANonempty I.hnB I.htargetCapB I.honeB I.hactiveABound
  have hrepB₂ : σ₂.arrs "repB" = arrOf n repB' :=
    (runA.frame_arr "repB" (by decide)).trans hrepB'
  have hactiveB₂ : σ₂.arrs "activeB" = arrOf n I.activeB :=
    (runA.frame_arr "activeB" (by decide)).trans hactiveB'
  have hrepsB₂ : σ₂.arrs "repsB" = arrOf n repsB' :=
    (runA.frame_arr "repsB" (by decide)).trans hrepsB'
  have hnextB₂ : σ₂.arrs "nextB" = arrOf n nextB' :=
    (runA.frame_arr "nextB" (by decide)).trans hnextB'
  have hnextBCount₂ : σ₂.vars "nextBCount" = R.card :=
    (runA.frame_var "nextBCount" (by decide)).trans hnextBCount
  have hrun := Run.seq runB runA
  let hB : ConcreteTracePartition G I.activeB (finSetAsSet Wnum) R repB' :=
    Classical.choice certB
  let hA : ConcreteTracePartition G I.activeA (finSetAsSet R) S repA' :=
    Classical.choice certA
  let Wfin := finsetOfNumeric (n := n) Wnum
  have hWset : (Wfin : Set (Fin n)) = finSetAsSet Wnum :=
    coe_finsetOfNumeric (n := n) Wnum
  let hBfin : ConcreteTracePartition G I.activeB (Wfin : Set (Fin n)) R repB' := by
    rw [hWset]
    exact hB
  have hBactiveSet : {v : Fin n | I.activeB v.val = 1} = (Bset : Set (Fin n)) := by
    ext v
    exact (I.hBactive v).symm
  have hAactiveSet : {v : Fin n | I.activeA v.val = 1} = (A : Set (Fin n)) := by
    ext v
    exact (I.hAactive v).symm
  let hBsource := reindexPartition hBfin.partition hBactiveSet.symm rfl
    (coe_finsetOfNumeric (n := n) R)
  let hAsource := reindexPartition hA.partition hAactiveSet.symm
    (coe_finsetOfNumeric (n := n) R) (coe_finsetOfNumeric (n := n) S)
  let contraction := concreteTraceContractionOfVerifiedPartitions
    G A Bset Wfin I.activeA I.activeB repA' repB' R S
    I.hAactive I.hBactive I.hWsubsetA hBfin hA
  refine ⟨σ₁, σ₂, currentB, currentA, R, S, labelB, repClassB,
    repsB', nextB', repB', labelA, repClassA, repsA', nextA', repA', hB, hA, ?_⟩
  refine ⟨runB, runA, hrun, dataB, dataA, hnextBCount, hnextACount,
    hnextBCount₂, ?_, hrepsB₂, hrepB₂, hnextB₂, hactiveA', hrepsA',
    hrepA', hnextA', ?_⟩
  · exact hactiveB₂
  · refine ⟨contraction, ?_, ?_, ?_, ?_, ?_⟩
    · intro b hb
      exact concreteTraceContractionOfVerifiedPartitions_bval
        G A Bset Wfin I.activeA I.activeB repA' repB' R S
        I.hAactive I.hBactive I.hWsubsetA hBfin hA b hb
    · intro a ha
      exact concreteTraceContractionOfVerifiedPartitions_aval
        G A Bset Wfin I.activeA I.activeB repA' repB' R S
        I.hAactive I.hBactive I.hWsubsetA hBfin hA a ha
    · change (traceContractionOfVerifiedPartitions G A Bset Wfin
        (finsetOfNumeric R) (finsetOfNumeric S) I.hWsubsetA
        hBsource hAsource).retainedB = finsetOfNumeric R
      exact traceContractionOfVerifiedPartitions_retainedB G A Bset Wfin
        (finsetOfNumeric R) (finsetOfNumeric S) I.hWsubsetA hBsource hAsource
    · change (traceContractionOfVerifiedPartitions G A Bset Wfin
        (finsetOfNumeric R) (finsetOfNumeric S) I.hWsubsetA
        hBsource hAsource).retainedA = finsetOfNumeric S
      exact traceContractionOfVerifiedPartitions_retainedA G A Bset Wfin
        (finsetOfNumeric R) (finsetOfNumeric S) I.hWsubsetA hBsource hAsource
    · have hcostB := partitionCost_le_input I.hx I.hsampleCountN
        (PrefixEnumerates.entry_lt I.henum I.hWrange)
        I.henum.injective_on_prefix
      have hRrange : ∀ v ∈ R, v < n := by
        intro v hv
        exact (mem_activeVertices.mp (dataB.reps_processed hv)).1
      have hRcard : R.card ≤ n := by
        calc
          R.card ≤ (Finset.range n).card := Finset.card_le_card (by
            intro v hv
            exact Finset.mem_range.mpr (hRrange v hv))
          _ = n := Finset.card_range n
      have hcostA := partitionCost_le_input I.hx hRcard
        (PrefixEnumerates.entry_lt dataB.enum hRrange)
        dataB.enum.injective_on_prefix
      omega

end

end Lax457868Proofs.VerifiedRoundPartitions
