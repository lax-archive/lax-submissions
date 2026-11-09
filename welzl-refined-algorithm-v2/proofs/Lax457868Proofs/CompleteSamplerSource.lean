import Lax457868Proofs.InitialSamplerRetriesSource
import Lax457868Proofs.ExceptionRepairLoop
import Lax457868Proofs.RepairClassOffsets
import Lax457868Proofs.SamplerContract

/-! The fixed source composition for the nontrivial refined-sampler branch. -/

namespace Lax457868Proofs.CompleteSamplerSource

open Lax808846Proofs.Imp
open Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.FullSamplePartition
open Lax457868Proofs.RepairClassOffsets
open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerOutputSize
open Lax457868Proofs.SamplerContract
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ExceptionRefinementStep
open Lax11.GraphEncoding

noncomputable section

private lemma array_length_after_initial
    {B n m domainCap r t bufferCap targetCap Q k cap cost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    {τ : Env}
    (hrun : Run B initialSamplerRetriesSource R.I.σ τ cost)
    {a : String} {len : ℕ} {f : ℕ → ℕ}
    (harray : R.I.σ.arrs a = arrOf len f) :
    (τ.arrs a).length = len := by
  rw [run_array_length_eq hrun a, harray]
  simp [arrOf]

/-- The accepted result becomes the input to the actual exception scan. All
scratch arrays are taken from their post-run lengths, without assigning them
mathematical contents. -/
private lemma accepted_exception_input
    {B n m domainCap r t bufferCap targetCap Q k cap cost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k cap G x A)
    {τ : Env}
    (hrun : Run B initialSamplerRetriesSource R.I.σ τ cost)
    (hn : τ.vars "n" = n)
    (haccepted : AcceptedResult G A
      (activeVertices n R.I.activeB) r k cap τ) :
    ∃ (choice : InitialChoice A (activeVertices n R.I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r),
      ∃ I : ExceptionPhaseSource.Input B n targetCap choice.sample.card
        G x A (choice.exceptions k) choice.sample,
        ∃ packedExceptions : ℕ → ℕ,
          I.σ = τ ∧ I.activeB = R.I.activeB ∧
          τ.vars "initialRetryStatus" = 1 ∧
          τ.arrs "exceptionList" = arrOf n packedExceptions ∧
          PrefixEnumerates (choice.exceptions k).card packedExceptions
            (choice.exceptions k) ∧
          (choice.exceptions k).card ≤ cap ∧
          ∀ b ∈ activeVertices n R.I.activeB,
            choice.representative b = I.repB b := by
  classical
  obtain ⟨rep, choice, packedExceptions, packedSample,
    hstatus, _hattempt, hrep, hrepChoice, hflags, hlist,
    hEprefix, hEcount, hsample, hord, hWprefix, hWcount, hcap⟩ := haccepted
  have arrLen {a : String} {len : ℕ} {f : ℕ → ℕ}
      (h : R.I.σ.arrs a = arrOf len f) : (τ.arrs a).length = len :=
    array_length_after_initial R hrun h
  obtain ⟨classB, hclassB⟩ := exists_arrOf_of_length (arrLen R.I.hclassB)
  obtain ⟨classSize, hclassSize⟩ := exists_arrOf_of_length (arrLen R.I.hclassSize)
  obtain ⟨markedCount, hmarkedCount⟩ :=
    exists_arrOf_of_length (arrLen R.I.hmarkedCount)
  obtain ⟨stamp, hstamp⟩ := exists_arrOf_of_length (arrLen R.I.hstamp)
  obtain ⟨marked, hmarked⟩ := exists_arrOf_of_length (arrLen R.I.hmarked)
  obtain ⟨touched, htouched⟩ := exists_arrOf_of_length (arrLen R.I.htouched)
  obtain ⟨split, hsplit⟩ := exists_arrOf_of_length (arrLen R.I.hsplit)
  have hWsubset : choice.sample ⊆ A := by
    intro a ha
    exact choice.draws_mem a (List.mem_toFinset.mp ha)
  have hErange : choice.exceptions k ⊆ Finset.range n := by
    intro b hb
    exact Finset.mem_range.mpr (mem_activeVertices.mp
      (Finset.mem_filter.mp hb).1).1
  have hWrange : choice.sample ⊆ Finset.range n :=
    hWsubset.trans R.I.hA
  have hWcard : choice.sample.card ≤ n := by
    simpa using Finset.card_le_card hWrange
  have hactiveA : τ.arrs "activeA" = arrOf n (setFlag A) := by
    rw [hrun.frame_arr "activeA" (by decide)]
    exact R.hactiveA
  have hactiveB : τ.arrs "activeB" = arrOf n R.I.activeB := by
    rw [hrun.frame_arr "activeB" (by decide)]
    exact R.I.hactiveB
  have hoff : τ.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [hrun.frame_arr "off" (by decide)]
    exact R.I.hoff
  have htgt : τ.arrs "tgt" = arrOf targetCap (target x) := by
    rw [hrun.frame_arr "tgt" (by decide)]
    exact R.I.htarget
  refine ⟨choice, {
    σ := τ
    activeB := R.I.activeB
    ord := packedSample
    classB := classB
    classSize := classSize
    markedCount := markedCount
    stamp := stamp
    marked := marked
    touched := touched
    split := split
    repB := rep
    hx := R.I.hx
    htargetCap := R.I.htargetCapEq
    hn := hn
    hsampleCount := hWcount
    hexceptionCount := hEcount
    hoff := hoff
    htarget := htgt
    hactiveA := hactiveA
    hactiveB := hactiveB
    hactiveE := hflags
    hsampleFlags := hsample
    hord := hord
    hclassB := hclassB
    hclassSize := hclassSize
    hmarkedCount := hmarkedCount
    hstamp := hstamp
    hmarked := hmarked
    htouched := htouched
    hsplit := hsplit
    hrepB := hrep
    henum := by simpa only [hWcount] using hWprefix
    hA := R.I.hA
    hE := hErange
    hW := hWrange
    hWA := hWsubset
    hsampleCountN := hWcard
    hnB := by have := R.I.hnPlusOneB; omega
    htargetCapB := R.I.htargetCapB
    honeB := R.I.honeB
  }, packedExceptions, rfl, rfl, hstatus, hlist,
    by simpa only [hEcount] using hEprefix, hcap, hrepChoice⟩

/-- On samples and scan vertices inside `A`, intersecting every neighborhood
with `A` does not change the phase-two decisions. -/
private lemma phase2Scan_restrict
    (N : ℕ → Finset ℕ) (E A W : Finset ℕ) (as : List ℕ)
    (hW : W ⊆ A) (has : ∀ a ∈ as, a ∈ A) :
    phase2Scan (fun b => N b ∩ A) E as W = phase2Scan N E as W := by
  classical
  induction as generalizing W with
  | nil => rfl
  | cons a rest ih =>
    have ha : a ∈ A := has a List.mem_cons_self
    have htrace (b : ℕ) :
        trace (fun b => N b ∩ A) W b = trace N W b := by
      ext v
      by_cases hv : v ∈ W
      · have hvA := hW hv
        simp [trace, hv, hvA]
      · simp [trace, hv]
    have hsplit : splitsExceptionPairB (fun b => N b ∩ A) E W a =
        splitsExceptionPairB N E W a := by
      have hprop : splitsExceptionPair (fun b => N b ∩ A) E W a ↔
          splitsExceptionPair N E W a := by
        simp only [splitsExceptionPair]
        constructor <;> rintro ⟨b, b', hb, hb', ht, hs⟩
        · exact ⟨b, b', hb, hb', by simpa only [htrace] using ht,
            by simpa only [Finset.mem_inter, ha, and_true] using hs⟩
        · exact ⟨b, b', hb, hb', by simpa only [htrace] using ht,
            by simpa only [Finset.mem_inter, ha, and_true] using hs⟩
      by_cases h : splitsExceptionPairB N E W a = true
      · have hp := (splitsExceptionPairB_eq_true_iff N E W a).mp h
        have hr := (splitsExceptionPairB_eq_true_iff
          (fun b => N b ∩ A) E W a).mpr (hprop.mpr hp)
        simp [h, hr]
      · have hr : splitsExceptionPairB (fun b => N b ∩ A) E W a = false := by
          cases hr : splitsExceptionPairB (fun b => N b ∩ A) E W a
          · rfl
          · have hp := (splitsExceptionPairB_eq_true_iff
              (fun b => N b ∩ A) E W a).mp hr
            have hs := (splitsExceptionPairB_eq_true_iff N E W a).mpr
              (hprop.mp hp)
            contradiction
        cases hn : splitsExceptionPairB N E W a <;> simp_all
    have hstep : phase2Step (fun b => N b ∩ A) E W a =
        phase2Step N E W a := by simp [phase2Step, hsplit]
    have hWstep : phase2Step N E W a ⊆ A := by
      simp only [phase2Step]
      split_ifs
      · exact Finset.insert_subset ha hW
      · exact hW
    have hasRest : ∀ v ∈ rest, v ∈ A := by
      intro v hv
      exact has v (List.mem_cons_of_mem a hv)
    simpa only [phase2Scan, hstep] using ih (W := phase2Step N E W a)
      hWstep hasRest

lemma phaseTwoSample_restrict {n : ℕ} (G : SimpleGraph (Fin n))
    (E A W : Finset ℕ) (hW : W ⊆ A) :
    phaseTwoSample G E A W =
      phase2Scan (fun b => numericNeighborhood G b ∩ A) E
        ((List.range n).filter fun a => a ∈ A) W := by
  unfold phaseTwoSample
  symm
  apply phase2Scan_restrict
  · exact hW
  · intro a ha
    simpa using (List.mem_filter.mp ha).2

/-- Recover the complete active-side partition input from the phase-two run.
Only array lengths, not stale scratch contents, are needed here. -/
private lemma phaseTwo_fullPartition_input
    {B n targetCap sampleCount cost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A E W : Finset ℕ}
    (I : ExceptionPhaseSource.Input B n targetCap sampleCount G x A E W)
    (hactiveCount : I.σ.vars "activeBCount" =
      (activeVertices n I.activeB).card)
    (hactiveBound : ∀ v < n, I.activeB v < B)
    {τ : Env} {packed : ℕ → ℕ}
    (hrun : Run B exceptionPhase I.σ τ cost)
    (hsample : τ.arrs "sampleFlags" =
      arrOf n (setFlag (phaseTwoSample G E A W)))
    (hord : τ.arrs "ord" = arrOf n packed)
    (hprefix : PrefixEnumerates (τ.vars "sampleCount") packed
      (phaseTwoSample G E A W))
    (hcount : τ.vars "sampleCount" = (phaseTwoSample G E A W).card)
    (hrep : τ.arrs "repB" = arrOf n I.repB)
    (hactive : τ.arrs "activeB" = arrOf n I.activeB)
    (hoff : τ.arrs "off" = arrOf (n + 1) (offset x))
    (htgt : τ.arrs "tgt" = arrOf targetCap (target x))
    (hn : τ.vars "n" = n) :
    ∃ P : FullSamplePartition.Input B n targetCap
      (phaseTwoSample G E A W).card G x (phaseTwoSample G E A W),
      P.σ = τ ∧ P.activeB = I.activeB ∧ P.repB = I.repB ∧
      P.ord = packed ∧
      P.sampleFlags = setFlag (phaseTwoSample G E A W) := by
  classical
  have arrLen {a : String} {f : ℕ → ℕ}
      (h : I.σ.arrs a = arrOf n f) : (τ.arrs a).length = n := by
    rw [run_array_length_eq hrun a, h]
    simp [arrOf]
  obtain ⟨classB, hclassB⟩ := exists_arrOf_of_length (arrLen I.hclassB)
  obtain ⟨classSize, hclassSize⟩ := exists_arrOf_of_length (arrLen I.hclassSize)
  obtain ⟨markedCount, hmarkedCount⟩ :=
    exists_arrOf_of_length (arrLen I.hmarkedCount)
  obtain ⟨stamp, hstamp⟩ := exists_arrOf_of_length (arrLen I.hstamp)
  obtain ⟨marked, hmarked⟩ := exists_arrOf_of_length (arrLen I.hmarked)
  obtain ⟨touched, htouched⟩ := exists_arrOf_of_length (arrLen I.htouched)
  obtain ⟨split, hsplit⟩ := exists_arrOf_of_length (arrLen I.hsplit)
  have hWnewA : phaseTwoSample G E A W ⊆ A := by
    unfold phaseTwoSample
    apply phase2Scan_subset_of_ground (numericNeighborhood G) E A
      ((List.range n).filter fun a => a ∈ A) W I.hWA
    intro a ha
    simpa using (List.mem_filter.mp ha).2
  have hWnewRange : phaseTwoSample G E A W ⊆ Finset.range n :=
    hWnewA.trans I.hA
  have hWnewCount : (phaseTwoSample G E A W).card ≤ n := by
    simpa using Finset.card_le_card hWnewRange
  have hactiveCount' : τ.vars "activeBCount" =
      (activeVertices n I.activeB).card := by
    rw [hrun.frame_var "activeBCount" (by decide)]
    exact hactiveCount
  refine ⟨{
    σ := τ
    activeB := I.activeB
    ord := packed
    classB := classB
    classSize := classSize
    markedCount := markedCount
    stamp := stamp
    marked := marked
    touched := touched
    split := split
    repB := I.repB
    sampleFlags := setFlag (phaseTwoSample G E A W)
    hx := I.hx
    htargetCap := I.htargetCap
    hn := hn
    hsampleCount := hcount
    hactiveBCount := hactiveCount'
    hoff := hoff
    htarget := htgt
    hactiveB := hactive
    hord := hord
    hclassB := hclassB
    hclassSize := hclassSize
    hmarkedCount := hmarkedCount
    hstamp := hstamp
    hmarked := hmarked
    htouched := htouched
    hsplit := hsplit
    hrepB := hrep
    hsampleFlags := hsample
    henum := by simpa only [hcount] using hprefix
    hWrange := hWnewRange
    hsampleCountN := hWnewCount
    hnB := I.hnB
    htargetCapB := I.htargetCapB
    honeB := I.honeB
    hactiveBBound := hactiveBound
  }, rfl, rfl, rfl, rfl, rfl⟩

/-- The full active-side partition is the grouping domain. The radix scratch
is recovered by length from the actual state. -/
private lemma partition_group_input
    {B n targetCap sampleCount Q q cost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {W : Finset ℕ}
    (I : FullSamplePartition.Input B n targetCap sampleCount G x W)
    (hQpow : I.σ.vars "qpow" = Q)
    (hcountLength : (I.σ.arrs "count").length = Q)
    (hscratchLength : (I.σ.arrs "scratchOrder").length = n)
    (hflags01 : ∀ v < n, I.activeB v ≤ 1)
    (hnQ : n ≤ Q) (hQB : Q < B)
    {τ : Env} {label size : ℕ → ℕ}
    (hrun : Run B fullSamplePartition I.σ τ cost)
    (hclassCount : τ.vars "classCount" = q) (hqLe : q ≤ n)
    (hlabel : τ.arrs "classB" = arrOf n label)
    (hsize : τ.arrs "classSize" = arrOf n size)
    (hsizes : ClassSizes n q I.activeB label size)
    (hactive : τ.arrs "activeB" = arrOf n I.activeB)
    (hrep : τ.arrs "repB" = arrOf n I.repB)
    (hsample : τ.arrs "sampleFlags" = arrOf n I.sampleFlags)
    (hord : τ.arrs "ord" = arrOf n I.ord)
    (hn : τ.vars "n" = n) :
    ∃ H : FullSamplePartition.GroupInput B n q Q,
      H.σ = τ ∧ H.active = I.activeB ∧ H.label = label ∧
      H.size = size ∧ H.ord = I.ord ∧ H.repB = I.repB ∧
      H.sampleFlags = I.sampleFlags := by
  classical
  have hcountLen : (τ.arrs "count").length = Q := by
    rw [run_array_length_eq hrun]
    exact hcountLength
  have hscratchLen : (τ.arrs "scratchOrder").length = n := by
    rw [run_array_length_eq hrun]
    exact hscratchLength
  obtain ⟨count, hcount⟩ := exists_arrOf_of_length hcountLen
  obtain ⟨scratch, hscratch⟩ := exists_arrOf_of_length hscratchLen
  refine ⟨{
    σ := τ
    active := I.activeB
    label := label
    size := size
    ord := I.ord
    count := count
    scratch := scratch
    repB := I.repB
    sampleFlags := I.sampleFlags
    hn := hn
    hqpow := by
      rw [hrun.frame_var "qpow" (by decide)]
      exact hQpow
    hclassCount := hclassCount
    hactive := hactive
    hlabel := hlabel
    hsize := hsize
    hord := hord
    hcount := hcount
    hscratch := hscratch
    hrepB := hrep
    hsampleFlags := hsample
    hsizes := hsizes
    hflags01 := hflags01
    hqQ := hqLe.trans hnQ
    hQB := hQB
    hnB := I.hnB
    honeB := I.honeB
  }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma full_partition_fibre
    (C E W : Finset ℕ) (N : ℕ → Finset ℕ)
    (xs : List ℕ) (label : ℕ → ℕ)
    (hxs : xs.toFinset = C) (hE : E ⊆ C)
    (hclass : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔ trace N W b = trace N W b'))
    (b : ℕ) (hb : b ∈ E) :
    labelClass xs label (label b) =
      C.filter (fun v => trace N W b = trace N W v) := by
  simpa [labelClass, hxs, Lax457868Proofs.SamplerInitialExpectation.fiberOn,
    eq_comm] using
    (labelClass_eq_traceFiberOn C label N W (label b) b rfl (hE hb) hclass)

private lemma grouped_class_total
    {n q : ℕ} (active label size : ℕ → ℕ) (xs : List ℕ)
    (hxsNodup : xs.Nodup)
    (hxsSet : xs.toFinset = activeVertices n active)
    (hsizes : ClassSizes n q active label size)
    (hstart : classStart size q = startDigit label xs q) :
    classStart size q = xs.length := by
  have hkey : ∀ x ∈ xs, label x < q := by
    intro x hx
    have hv : x ∈ activeVertices n active := by
      rw [← hxsSet]
      exact List.mem_toFinset.mpr hx
    obtain ⟨hxn, hflag⟩ := mem_activeVertices.mp hv
    exact hsizes.1 x hxn hflag
  rw [hstart, ← length_bucketSort_eq_startDigit]
  exact (bucketSort_perm hxsNodup hkey).length_eq

/-- Restore the local repair sample size from its runtime register. Initial
representative selection can change `batchTarget` to a class size. -/
def setupRepairSampleSize : Com :=
  .assign "batchTarget" (.var "repairSampleSize")

/-- The accepted branch of the fixed source. -/
def prepareRepairSource : Com :=
  seqs [exceptionPhase, fullSamplePartition, groupActiveB,
    repairClassOffsets, setupRepairSampleSize]

def completeSamplerTail : Com :=
  prepareRepairSource.seq exceptionRepairPackedSource

/-- One fixed program. Later phases execute only after an accepted initial
attempt; each phase-three local failure remains visible in its status register. -/
def completeSamplerSource : Com :=
  initialSamplerRetriesSource.seq
    (.ite (.eq (.var "initialRetryStatus") (.lit 1))
      completeSamplerTail
      .skip)

/-- Extra factual registers and workspace arrays used only by phase three.
The sampler's initial scratch arrays remain those in `ReadyInput`. -/
structure RuntimeInput
    {B n m domainCap r t bufferCap targetCap Q k initialCap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (s repairCap : ℕ) where
  hdomainCap : domainCap = n
  hsampleSize : R.I.σ.vars "repairSampleSize" = s
  hrepairCap : R.I.σ.vars "repairRetryCap" = repairCap
  hfarBound : R.I.σ.vars "repairFarBound" = (2 * k) / 3
  hstartLength : (R.I.σ.arrs "repairClassStart").length = n
  htrialZero : R.I.σ.arrs "trialActive" = arrOf n (fun _ => 0)
  hrowZero : R.I.σ.arrs "trialRowMarks" = arrOf n (fun _ => 0)
  hdesiredZero : R.I.σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0)
  hrowLength : (R.I.σ.arrs "trialRowList").length = n
  hdesiredLength : (R.I.σ.arrs "trialDesiredList").length = n
  hdiffLength : (R.I.σ.arrs "trialDiffList").length = n
  hBListLength : (R.I.σ.arrs "repairBList").length = n
  hRListLength : (R.I.σ.arrs "repairRList").length = n
  hBMarksZero : R.I.σ.arrs "repairBMarks" = arrOf n (fun _ => 0)
  hRMarksZero : R.I.σ.arrs "repairRMarks" = arrOf n (fun _ => 0)
  hsBuffer : s ≤ bufferCap
  hsB : s < B
  hrepairCapB : repairCap < B
  hfarB : (2 * k) / 3 < B

private lemma setupRepairSampleSize_run {B s : ℕ} {σ : Env}
    (hsize : σ.vars "repairSampleSize" = s) (hsB : s < B) :
    Run B setupRepairSampleSize σ (σ.setVar "batchTarget" s) 2 := by
  apply Run.assign
  rw [evalB_var_iff]
  exact ⟨hsize.symm, by rw [hsize]; exact hsB⟩


/-- Build the phase-three record from one executed initial-and-preparation
prefix. All physical array facts refer to its actual final environment. -/
private lemma prepared_loop_input
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      q cost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    (choice : InitialChoice A (activeVertices n R.I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r)
    {τ : Env} (hrun : Run B
      (initialSamplerRetriesSource.seq prepareRepairSource) R.I.σ τ cost)
    (bits : List Bool) (hinput : τ.inp = bits.map Bool.toNat ++ R.I.rest)
    (exceptionList rep label size ord starts : ℕ → ℕ)
    (xs : List ℕ)
    (hlist : τ.arrs "exceptionList" = arrOf n exceptionList)
    (hprefix : PrefixEnumerates (choice.exceptions k).card exceptionList
      (choice.exceptions k))
    (hrep : τ.arrs "repB" = arrOf n rep)
    (hrepChoice : ∀ b ∈ activeVertices n R.I.activeB,
      choice.representative b = rep b)
    (hsample : τ.arrs "sampleFlags" =
      arrOf n (setFlag (phaseTwoSample G (choice.exceptions k) A choice.sample)))
    (hlabelArr : τ.arrs "classB" = arrOf n label)
    (hsizeArr : τ.arrs "classSize" = arrOf n size)
    (hstartArr : τ.arrs "repairClassStart" = arrOf n starts)
    (hord : τ.arrs "ord" = arrOf n ord)
    (hclassCount : τ.vars "classCount" = q)
    (hexceptionCount : τ.vars "exceptionCount" = (choice.exceptions k).card)
    (hbatch : τ.vars "batchTarget" = s)
    (hn : τ.vars "n" = n) (hqpow : τ.vars "qpow" = Q)
    (hsizes : ClassSizes n q R.I.activeB label size)
    (hclassify : ∀ b ∈ activeVertices n R.I.activeB,
      ∀ b' ∈ activeVertices n R.I.activeB,
        (label b = label b' ↔
          trace (numericNeighborhood G)
            (phaseTwoSample G (choice.exceptions k) A choice.sample) b =
          trace (numericNeighborhood G)
            (phaseTwoSample G (choice.exceptions k) A choice.sample) b'))
    (hxsSet : xs.toFinset = activeVertices n R.I.activeB)
    (hxsCard : xs.length = (activeVertices n R.I.activeB).card)
    (hslice : ∀ d < q, PrefixEnumerates (size d)
      (fun i => ord (classStart size d + i)) (labelClass xs label d))
    (hstarts : ∀ d < q, starts d = classStart size d)
    (hends : ∀ d < q, classStart size d + size d ≤ xs.length)
    (hqLe : q ≤ n) :
    ∃ L : LoopInput B n s t bufferCap targetCap q repairCap k
      (choice.exceptions k).card G x (choice.exceptions k)
      (activeVertices n R.I.activeB)
      (phaseTwoSample G (choice.exceptions k) A choice.sample)
      A (phaseTwoSample G (choice.exceptions k) A choice.sample),
      L.σ = τ ∧ L.bits = bits ∧ L.rest = R.I.rest ∧
      L.rep = rep ∧ L.exceptionList = exceptionList := by
  classical
  let C := activeVertices n R.I.activeB
  let E := choice.exceptions k
  let W₂ := phaseTwoSample G E A choice.sample
  have hEsub : E ⊆ C := Finset.filter_subset _ _
  have hCsub : C ⊆ Finset.range n := by
    intro b hb
    exact Finset.mem_range.mpr (mem_activeVertices.mp hb).1
  have hErange : E ⊆ Finset.range n := hEsub.trans hCsub
  have hWinitialA : choice.sample ⊆ A := by
    intro a ha
    exact choice.draws_mem a (List.mem_toFinset.mp ha)
  have hW₂A : W₂ ⊆ A := by
    unfold W₂ phaseTwoSample
    apply phase2Scan_subset_of_ground (numericNeighborhood G) E A
      ((List.range n).filter fun a => a ∈ A) choice.sample hWinitialA
    intro a ha
    simpa using (List.mem_filter.mp ha).2
  have hEcard : E.card ≤ n := by
    exact (Finset.card_le_card hErange).trans (by simp)
  have hCcard : C.card ≤ n := by
    exact activeVertices_card_le n R.I.activeB
  have hinputRaw : (R.I.σ.arrs "drawDomain").length = n := by
    rw [R.I.hdrawDomain]
    simp [arrOf, S.hdomainCap]
  have arrLength {a : String} {len : ℕ}
      (h : (R.I.σ.arrs a).length = len) : (τ.arrs a).length = len := by
    rw [run_array_length_eq hrun]
    exact h
  have arrFrame {a : String} (ha : a ∉
      (initialSamplerRetriesSource.seq prepareRepairSource).warrs) :
      τ.arrs a = R.I.σ.arrs a := hrun.frame_arr a ha
  have varFrame {v : String} (hv : v ∉
      (initialSamplerRetriesSource.seq prepareRepairSource).wvars) :
      τ.vars v = R.I.σ.vars v := hrun.frame_var v hv
  have hactiveA : τ.arrs "activeA" = arrOf n (setFlag A) := by
    rw [arrFrame (a := "activeA") (by decide)]
    exact R.hactiveA
  have hactiveB : τ.arrs "activeB" = arrOf n R.I.activeB := by
    rw [arrFrame (a := "activeB") (by decide)]
    exact R.I.hactiveB
  have hoff : τ.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [arrFrame (a := "off") (by decide)]
    exact R.I.hoff
  have htgt : τ.arrs "tgt" = arrOf targetCap (target x) := by
    rw [arrFrame (a := "tgt") (by decide)]
    exact R.I.htarget
  have hpow : τ.vars "qpow" < B := by
    rw [hqpow]
    exact R.I.hQltB
  have hdrawCap : τ.vars "drawCap" = t := by
    rw [varFrame (v := "drawCap") (by decide)]
    exact R.I.hdrawCap
  have hrepairCap : τ.vars "repairRetryCap" = repairCap := by
    rw [varFrame (v := "repairRetryCap") (by decide)]
    exact S.hrepairCap
  have hfar : τ.vars "repairFarBound" = (2 * k) / 3 := by
    rw [varFrame (v := "repairFarBound") (by decide)]
    exact S.hfarBound
  have htrialZero : τ.arrs "trialActive" = arrOf n (fun _ => 0) := by
    rw [arrFrame (a := "trialActive") (by decide)]
    exact S.htrialZero
  have hrowZero : τ.arrs "trialRowMarks" = arrOf n (fun _ => 0) := by
    rw [arrFrame (a := "trialRowMarks") (by decide)]
    exact S.hrowZero
  have hdesiredZero : τ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) := by
    rw [arrFrame (a := "trialDesiredMarks") (by decide)]
    exact S.hdesiredZero
  have hBMarksZero : τ.arrs "repairBMarks" = arrOf n (fun _ => 0) := by
    rw [arrFrame (a := "repairBMarks") (by decide)]
    exact S.hBMarksZero
  have hRMarksZero : τ.arrs "repairRMarks" = arrOf n (fun _ => 0) := by
    rw [arrFrame (a := "repairRMarks") (by decide)]
    exact S.hRMarksZero
  have hxsRange : xs.toFinset ⊆ Finset.range n := by
    rw [hxsSet]
    exact hCsub
  have hlabelRange : ∀ b ∈ E, label b < q := by
    intro b hb
    obtain ⟨hbn, hflag⟩ := mem_activeVertices.mp (hEsub hb)
    exact hsizes.1 b hbn hflag
  have hrepRange : ∀ b ∈ E, rep b < n := by
    intro b hb
    rw [← hrepChoice b (hEsub hb)]
    exact (mem_activeVertices.mp
      (choice.representative_mem b (hEsub hb))).1
  have hnpos : 0 < n := by
    obtain ⟨a, ha⟩ := R.I.hAnonempty
    exact Nat.pos_of_ne_zero (by
      intro hz
      have := R.I.hA ha
      simp [hz] at this)
  refine ⟨{
    σ := τ
    bits := bits
    rest := R.I.rest
    exceptionList := exceptionList
    rep := rep
    size := size
    starts := starts
    label := label
    ord := ord
    groupActive := R.I.activeB
    xs := xs
    hgraph := R.I.hx
    htargetCap := R.I.htargetCapEq
    hinput := hinput
    hn := hn
    hqpow := hpow
    htarget := hbatch
    hdrawCap := hdrawCap
    hclassCount := hclassCount
    hretryCap := hrepairCap
    hfarBound := hfar
    hexceptionCount := hexceptionCount
    hexceptionList := hlist
    hprefix := hprefix
    hrep := hrep
    hactive := hactiveA
    hdrawDomainLength := arrLength hinputRaw
    hkeyLength := arrLength (by rw [R.I.hkey0]; simp [arrOf])
    hdrawsLength := arrLength (by rw [R.I.hsampleDraws]; simp [arrOf])
    hsample := hsample
    htrialZero := htrialZero
    hrowZero := hrowZero
    hdesiredZero := hdesiredZero
    hrowLength := arrLength S.hrowLength
    hdesiredLength := arrLength S.hdesiredLength
    hdiffLength := arrLength S.hdiffLength
    hBListLength := arrLength S.hBListLength
    hRListLength := arrLength S.hRListLength
    hBMarksZero := hBMarksZero
    hRMarksZero := hRMarksZero
    hclassB := hlabelArr
    hclassSize := hsizeArr
    hclassStart := hstartArr
    hord := hord
    hoff := hoff
    htgt := htgt
    hgroupActive := hactiveB
    hxsCard := hxsCard
    hxsRange := hxsRange
    hactiveCard := hCcard
    hslice := hslice
    hstartTable := hstarts
    hclassEnd := hends
    hclassFibre := by
      intro b hb
      exact full_partition_fibre C E W₂ (numericNeighborhood G)
        xs label hxsSet hEsub hclassify b hb
    hlabel := hlabelRange
    hrepRange := hrepRange
    hErange := hErange
    hEgroup := hEsub
    hA := R.I.hA
    hWbase := Finset.Subset.rfl
    hWcurrentA := hW₂A
    heLe := hEcard
    hqLe := hqLe
    hn1B := R.I.hnPlusOneB
    htargetCapB := R.I.htargetCapB
    hbuffer := S.hsBuffer
    hsB := S.hsB
    htB := R.I.htB
    hcapB := S.hrepairCapB
    hfarB := S.hfarB
    hpowB := R.I.hpowN
    hthreeB := by have := R.hnB; omega
  }, rfl, rfl, rfl, rfl, rfl⟩

/-- Execute the five checked preparation stages from an accepted initial
state, and expose the actual phase-three input and additive stage charge. -/
lemma accepted_preparation_run
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      initialCost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    {τ : Env} (rinitial : Run B initialSamplerRetriesSource R.I.σ τ initialCost)
    (hnInitial : τ.vars "n" = n) (hqInitial : τ.vars "qpow" = Q)
    (bits : List Bool) (hinputInitial : τ.inp = bits.map Bool.toNat ++ R.I.rest)
    (haccepted : AcceptedResult G A
      (activeVertices n R.I.activeB) r k initialCap τ) :
    ∃ choice : InitialChoice A (activeVertices n R.I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r,
      ∃ q : ℕ,
      ∃ L : LoopInput B n s t bufferCap targetCap q repairCap k
        (choice.exceptions k).card G x (choice.exceptions k)
        (activeVertices n R.I.activeB)
        (phaseTwoSample G (choice.exceptions k) A choice.sample)
        A (phaseTwoSample G (choice.exceptions k) A choice.sample),
      ∃ phaseCost partitionCost groupCost offsetCost : ℕ,
      ∃ initialPacked phaseTwoPacked : ℕ → ℕ,
        Run B prepareRepairSource τ L.σ
          (phaseCost + partitionCost + groupCost + offsetCost + 2) ∧
        phaseCost = exceptionPhaseCost x initialPacked n choice.sample.card targetCap ∧
        partitionCost = fullSamplePartitionCost x phaseTwoPacked n
          (phaseTwoSample G (choice.exceptions k) A choice.sample).card ∧
        groupCost = 20 * n + 9 +
          64 * ((activeVertices n R.I.activeB).card + Q + 1) ∧
        offsetCost = 18 * q + 8 ∧
        PrefixEnumerates choice.sample.card initialPacked choice.sample ∧
        PrefixEnumerates
          (phaseTwoSample G (choice.exceptions k) A choice.sample).card
          phaseTwoPacked
          (phaseTwoSample G (choice.exceptions k) A choice.sample) ∧
        L.σ.vars "qpow" = Q ∧
        L.bits = bits ∧
        L.rest = R.I.rest ∧
        τ.vars "initialRetryStatus" = 1 ∧
        (choice.exceptions k).card ≤ initialCap ∧
        (∀ b ∈ activeVertices n R.I.activeB,
          choice.representative b = L.rep b) ∧
        phaseCost + partitionCost + groupCost + offsetCost + 2 ≤
          1229*n+987*targetCap+64*Q+571 := by
  classical
  obtain ⟨choice, I, exList, hIσ, hIactive, hstatus, hlist,
    hEprefix, hcap, hrepChoice⟩ :=
    accepted_exception_input R rinitial hnInitial haccepted
  obtain ⟨σ₂, packed₂, label₂, size₂, rphase,
    hsample₂, hord₂, hprefix₂, hcount₂, _hclass₂, _hsize₂,
    _hclassify₂, _hactiveA₂, _hflagsE₂, hactiveB₂, hrep₂,
    hoff₂, htgt₂, hn₂, _hEcount₂, _hinp₂, _hout₂,
    _harrFrame₂, _hvarFrame₂⟩ := exceptionPhase_run I
  have hactiveCountI : I.σ.vars "activeBCount" =
      (activeVertices n I.activeB).card := by
    rw [hIσ, hIactive]
    rw [rinitial.frame_var "activeBCount" (by decide)]
    exact R.I.hactiveBCount
  have hactiveBound : ∀ v < n, I.activeB v < B := by
    intro v hv
    rw [hIactive]
    have h01 := R.I.hactive01 v hv
    have hB := R.I.honeB
    omega
  obtain ⟨P, hPσ, hPactive, hPrep, hPord, hPsample⟩ :=
    phaseTwo_fullPartition_input I hactiveCountI hactiveBound
      rphase hsample₂ hord₂ hprefix₂ hcount₂ hrep₂ hactiveB₂
      hoff₂ htgt₂ hn₂
  obtain ⟨σ₃, q, label₃, size₃, rpart,
    hclassCount₃, hqLe, hclassB₃, hclassSize₃,
    hsizes₃, _hoccupied₃, hclassify₃, hactiveB₃,
    hsample₃, hord₃, hrep₃, _hoff₃, _htgt₃, hn₃,
    _hsampleCount₃, _hactiveCount₃, _hinp₃, _hout₃,
    _harrFrame₃, _hvarFrame₃⟩ := fullSamplePartition_run P
  have hqP : P.σ.vars "qpow" = Q := by
    rw [hPσ, rphase.frame_var "qpow" (by decide), hIσ]
    exact hqInitial
  have rinitialI : Run B initialSamplerRetriesSource R.I.σ I.σ
      initialCost := by simpa [hIσ] using rinitial
  have rinitialPhase : Run B
      (initialSamplerRetriesSource.seq exceptionPhase) R.I.σ σ₂
      (initialCost + exceptionPhaseCost x I.ord n choice.sample.card targetCap) :=
    rinitialI.seq rphase
  have hcountLenP : (P.σ.arrs "count").length = Q := by
    rw [hPσ, run_array_length_eq rinitialPhase, R.I.hcount]
    simp [arrOf]
  have hscratchLenP : (P.σ.arrs "scratchOrder").length = n := by
    rw [hPσ, run_array_length_eq rinitialPhase, R.I.hscratch]
    simp [arrOf]
  have hflags01 : ∀ v < n, P.activeB v ≤ 1 := by
    simpa only [hPactive, hIactive] using R.I.hactive01
  obtain ⟨H, hHσ, hHactive, hHlabel, hHsize, hHord,
    hHrep, hHsample⟩ :=
    partition_group_input P hqP hcountLenP hscratchLenP hflags01
      R.I.hQle R.I.hQltB rpart hclassCount₃ hqLe
      hclassB₃ hclassSize₃ hsizes₃ hactiveB₃ hrep₃ hsample₃
      hord₃ hn₃
  obtain ⟨σ₄, xs, sorted, rgroup,
    hxsNodup, hxsSet, hxsCard, _halen₄,
    hclassCount₄, hqpow₄, hord₄, _hsorted₄,
    _hsizeCount₄, hstartsMath, hends, hslice,
    hactiveB₄, hclassB₄, hclassSize₄, hrep₄,
    hsample₄, hn₄, _hcursor₄, _hsampleCount₄,
    _hinp₄, _hout₄, _harrFrame₄, _hvarFrame₄⟩ :=
    groupActiveB_run H
  have htotal : classStart H.size q ≤ n := by
    rw [grouped_class_total H.active H.label H.size xs
      hxsNodup hxsSet H.hsizes (hstartsMath q (Nat.le_refl q))]
    rw [hxsCard]
    exact activeVertices_card_le n H.active
  have rpart₂ : Run B fullSamplePartition σ₂ σ₃
      (fullSamplePartitionCost x P.ord n
        (phaseTwoSample G (choice.exceptions k) A choice.sample).card) := by
    simpa [hPσ] using rpart
  have rgroup₃ : Run B groupActiveB σ₃ σ₄
      (20 * n + 9 + 64 * ((activeVertices n H.active).card + Q + 1)) := by
    simpa [hHσ] using rgroup
  have rthroughGroup : Run B
      ((initialSamplerRetriesSource.seq exceptionPhase).seq
        (fullSamplePartition.seq groupActiveB))
      R.I.σ σ₄
      ((initialCost + exceptionPhaseCost x I.ord n choice.sample.card targetCap) +
        (fullSamplePartitionCost x P.ord n
          (phaseTwoSample G (choice.exceptions k) A choice.sample).card +
          (20 * n + 9 + 64 * ((activeVertices n H.active).card + Q + 1)))) :=
    rinitialPhase.seq (rpart₂.seq rgroup₃)
  have hstartLen₄ : (σ₄.arrs "repairClassStart").length = n := by
    rw [run_array_length_eq rthroughGroup]
    exact S.hstartLength
  obtain ⟨oldStart, hOldStart⟩ := exists_arrOf_of_length hstartLen₄
  obtain ⟨σ₅, roffset, hstarts₅, _hstartBound₅,
    _hcursor₅, _htotal₅, hsize₅, hArrFrame₅,
    hVarFrame₅, _hinp₅, _hout₅⟩ :=
    repairClassOffsets_run (B := B) (n := n) (q := q) (σ := σ₄)
      (size := H.size) (oldStart := oldStart)
      hclassCount₄ hclassSize₄ hOldStart
      hqLe htotal (by have := R.I.hnPlusOneB; omega)
  have hsampleSize₅ : σ₅.vars "repairSampleSize" = s := by
    rw [hVarFrame₅ "repairSampleSize" (by decide) (by decide) (by decide)]
    have hthrough := rthroughGroup.frame_var "repairSampleSize" (by decide)
    rw [hthrough]
    exact S.hsampleSize
  let σ₆ := σ₅.setVar "batchTarget" s
  have rsetup : Run B setupRepairSampleSize σ₅ σ₆ 2 :=
    setupRepairSampleSize_run hsampleSize₅ S.hsB
  have hphaseτ : Run B exceptionPhase τ σ₂
      (exceptionPhaseCost x I.ord n choice.sample.card targetCap) := by
    simpa [hIσ] using rphase
  let phaseCost := exceptionPhaseCost x I.ord n choice.sample.card targetCap
  let partitionCost := fullSamplePartitionCost x P.ord n
    (phaseTwoSample G (choice.exceptions k) A choice.sample).card
  let groupCost := 20 * n + 9 +
    64 * ((activeVertices n H.active).card + Q + 1)
  let offsetCost := 18 * q + 8
  have rprep : Run B prepareRepairSource τ σ₆
      (phaseCost + partitionCost + groupCost + offsetCost + 2) := by
    have h := hphaseτ.seq (rpart₂.seq (rgroup₃.seq (roffset.seq rsetup)))
    change Run B prepareRepairSource τ σ₆
      (phaseCost + (partitionCost + (groupCost + (offsetCost + 2)))) at h
    exact h.mono (by omega)
  have rwhole : Run B
      (initialSamplerRetriesSource.seq prepareRepairSource) R.I.σ σ₆
      (initialCost +
        (phaseCost + partitionCost + groupCost + offsetCost + 2)) :=
    rinitial.seq rprep
  have hlist₆ : σ₆.arrs "exceptionList" = arrOf n exList := by
    rw [rprep.frame_arr "exceptionList" (by decide)]
    exact hlist
  have hrep₆ : σ₆.arrs "repB" = arrOf n I.repB := by
    rw [rprep.frame_arr "repB" (by decide)]
    rw [← hIσ]
    exact I.hrepB
  have hsample₆ : σ₆.arrs "sampleFlags" =
      arrOf n (setFlag (phaseTwoSample G (choice.exceptions k) A choice.sample)) := by
    rw [rsetup.frame_arr "sampleFlags" (by decide)]
    rw [hArrFrame₅ "sampleFlags" (by decide)]
    simpa [hHsample, hPsample] using hsample₄
  have hclassB₆ : σ₆.arrs "classB" = arrOf n label₃ := by
    rw [rsetup.frame_arr "classB" (by decide)]
    rw [hArrFrame₅ "classB" (by decide)]
    simpa [hHlabel] using hclassB₄
  have hclassSize₆ : σ₆.arrs "classSize" = arrOf n size₃ := by
    rw [rsetup.frame_arr "classSize" (by decide)]
    simpa [hHsize] using hsize₅
  have hstarts₆ : σ₆.arrs "repairClassStart" =
      arrOf n (fun d => if d < q then classStart size₃ d else oldStart d) := by
    rw [rsetup.frame_arr "repairClassStart" (by decide)]
    simpa [hHsize] using hstarts₅
  have hord₆ : σ₆.arrs "ord" = arrOf n sorted := by
    rw [rsetup.frame_arr "ord" (by decide)]
    rw [hArrFrame₅ "ord" (by decide)]
    exact hord₄
  have hcount₆ : σ₆.vars "classCount" = q := by
    rw [rsetup.frame_var "classCount" (by decide)]
    rw [hVarFrame₅ "classCount" (by decide) (by decide) (by decide)]
    exact hclassCount₄
  have hEcount₆ : σ₆.vars "exceptionCount" =
      (choice.exceptions k).card := by
    rw [rprep.frame_var "exceptionCount" (by decide), ← hIσ]
    exact I.hexceptionCount
  have hn₆ : σ₆.vars "n" = n := by
    rw [rsetup.frame_var "n" (by decide)]
    rw [hVarFrame₅ "n" (by decide) (by decide) (by decide)]
    exact hn₄
  have hqpow₆ : σ₆.vars "qpow" = Q := by
    rw [rsetup.frame_var "qpow" (by decide)]
    rw [hVarFrame₅ "qpow" (by decide) (by decide) (by decide)]
    exact hqpow₄
  have hinput₆ : σ₆.inp = bits.map Bool.toNat ++ R.I.rest := by
    rw [rprep.frame_inp (by decide)]
    exact hinputInitial
  have hsizes₃' : ClassSizes n q R.I.activeB label₃ size₃ := by
    simpa [hPactive, hIactive] using hsizes₃
  have hclassify₃' : ∀ b ∈ activeVertices n R.I.activeB,
      ∀ b' ∈ activeVertices n R.I.activeB,
        (label₃ b = label₃ b' ↔
          trace (numericNeighborhood G)
            (phaseTwoSample G (choice.exceptions k) A choice.sample) b =
          trace (numericNeighborhood G)
            (phaseTwoSample G (choice.exceptions k) A choice.sample) b') := by
    simpa [hPactive, hIactive] using hclassify₃
  obtain ⟨L, hLσ, hLbits, hLrest, hLrep, hLlist⟩ :=
    prepared_loop_input R S choice rwhole bits hinput₆
      exList I.repB label₃ size₃ sorted
      (fun d => if d < q then classStart size₃ d else oldStart d) xs
      hlist₆ hEprefix hrep₆
      (by simpa [hIactive] using hrepChoice)
      hsample₆ hclassB₆ hclassSize₆ hstarts₆ hord₆
      hcount₆ hEcount₆ (by simp [σ₆]) hn₆ hqpow₆
      hsizes₃' hclassify₃'
      (by simpa [hHactive, hPactive, hIactive] using hxsSet)
      (by simpa [hHactive, hPactive, hIactive] using hxsCard)
      (by simpa [hHsize, hHlabel] using hslice)
      (by intro d hd; simp [hd])
      (by simpa [hHsize] using hends) hqLe
  refine ⟨choice, q, L, phaseCost, partitionCost, groupCost, offsetCost,
    I.ord, P.ord, ?_, rfl, rfl, ?_, rfl, I.henum, P.henum,
    ?_, hLbits, hLrest, hstatus, hcap, ?_, ?_⟩
  · simpa [hLσ] using rprep
  · simp [groupCost, hHactive, hPactive, hIactive]
  · simpa [hLσ] using hqpow₆
  · intro b hb
    rw [hLrep]
    exact hrepChoice b hb

  · have hi := I.exceptionPhaseCost_le_linear
    have hp := P.fullSamplePartitionCost_le_linear
    have hwi : choice.sample.card ≤ n := by
      simpa using Finset.card_le_card I.hW
    have hwp : (phaseTwoSample G (choice.exceptions k) A choice.sample).card ≤ n := by
      simpa using Finset.card_le_card P.hWrange
    have hactive : (activeVertices n H.active).card ≤ n := by
      apply (Finset.card_le_card ?_).trans (by simp : (Finset.range n).card ≤ n)
      intro v hv
      exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
    simp only [Cond.size, Expr.size] at hi hp
    dsimp [phaseCost, partitionCost, groupCost, offsetCost]
    omega

/-- A successful concrete phase-three trace yields the standard refined
sample contract, using the accepted initial choice as a singleton attempt. -/
private lemma successful_trace_refined_sample
    {n r cap k s c : ℕ} (G : SimpleGraph (Fin n))
    (A C Wfinal : Finset ℕ)
    (hA : A ⊆ Finset.range n)
    (hC : C.Nonempty) (hlarge : k < A.card)
    (hc : 0 < c)
    (hr : r = A.card / (4 * c ^ 2))
    (hcap : cap = A.card / (4 * c ^ 2 * (s + 1)))
    (choice : InitialChoice A C
      (fun b => numericNeighborhood G b ∩ A) r)
    (haccepted : (choice.exceptions k).card ≤ cap)
    (order : List ℕ)
    (horder : order.toFinset = choice.exceptions k)
    (hnodup : order.Nodup)
    (trials : ∀ b : ℕ, List (LocalTrial
      (((numericNeighborhood G b ∩ A) \
        (numericNeighborhood G (choice.representative b) ∩ A)) ∪
       ((numericNeighborhood G (choice.representative b) ∩ A) \
        (numericNeighborhood G b ∩ A))) s))
    (hscan : phase3Scan (fun b => numericNeighborhood G b ∩ A)
      C choice.representative k s trials order
      (phaseTwoSample G (choice.exceptions k) A choice.sample)
      (phaseTwoSample G (choice.exceptions k) A choice.sample) = some Wfinal) :
    Lax457868Proofs.RefinedSampleSpec.IsRefinedSample
      (neighborhoodFamily C (fun b => numericNeighborhood G b ∩ A))
      (A : Set ℕ) (Wfinal : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k := by
  classical
  let N : ℕ → Finset ℕ := fun b => numericNeighborhood G b ∩ A
  let groundOrder : List ℕ := (List.range n).filter fun a => a ∈ A
  have hground : groundOrder.toFinset = A := by
    ext a
    simp [groundOrder, List.toFinset_filter]
    intro ha
    exact Finset.mem_range.mp (hA ha)
  have hgroundNodup : groundOrder.Nodup := by
    exact (List.nodup_range (n := n)).filter _
  let repairTrials : ∀ ch : InitialChoice A C N r, ∀ b : ℕ,
      List (LocalTrial
        ((N b \ N (ch.representative b)) ∪
          (N (ch.representative b) \ N b)) s) :=
    fun ch b => if h : ch = choice then by subst ch; exact trials b else []
  let exceptionOrder : ∀ ch : InitialChoice A C N r, List ℕ :=
    fun ch => if ch = choice then order else (ch.exceptions k).toList
  have horderset : ∀ ch : InitialChoice A C N r,
      (exceptionOrder ch).toFinset = ch.exceptions k := by
    intro ch
    by_cases h : ch = choice
    · subst ch
      simpa [exceptionOrder] using horder
    · simp [exceptionOrder, h]
  have horderNodup : ∀ ch : InitialChoice A C N r,
      (exceptionOrder ch).Nodup := by
    intro ch
    by_cases h : ch = choice
    · subst ch
      simpa [exceptionOrder] using hnodup
    · change (if ch = choice then order else (ch.exceptions k).toList).Nodup
      rw [if_neg h]
      exact Finset.nodup_toList (ch.exceptions k)
  have hchoice : chooseInitialAttempt [choice] k cap = some choice := by
    simp [chooseInitialAttempt, haccepted]
  have hphase2 : phaseTwoSample G (choice.exceptions k) A choice.sample =
      phase2Scan N (choice.exceptions k) groundOrder choice.sample := by
    simpa [groundOrder, N] using
      phaseTwoSample_restrict G (choice.exceptions k) A choice.sample
        (by
          intro a ha
          exact choice.draws_mem a (List.mem_toFinset.mp ha))
  have htrial : repairTrials choice = trials := by
    funext b
    simp [repairTrials]
  have horderChoice : exceptionOrder choice = order := by
    simp [exceptionOrder]
  have hthree : runThreePhases A C N r cap k s [choice]
      groundOrder hground hgroundNodup repairTrials exceptionOrder
      horderset horderNodup = some Wfinal := by
    simp only [runThreePhases, hchoice]
    simpa only [← hphase2, htrial, horderChoice] using hscan
  have hret : refinedSampler A C N r cap k s [choice]
      groundOrder hground hgroundNodup repairTrials exceptionOrder
      horderset horderNodup = some Wfinal := by
    unfold refinedSampler
    simp only [show ¬ (A.card ≤ k ∨ C = ∅) from by
      intro h
      rcases h with h | h
      · omega
      · exact Finset.nonempty_iff_ne_empty.mp hC h,
      ↓reduceIte]
    exact hthree
  apply refinedSampler_IsRefinedSample A C N r cap k s c [choice]
    groundOrder hground hgroundNodup repairTrials exceptionOrder
    horderset horderNodup hc hr hcap
  · intro b hb
    exact Finset.inter_subset_right
  · exact hret

/-- The accepted choice determines representatives only on active vertices.
Replace its irrelevant off-domain values with the physical `repB` contents so
the local-repair trace has exactly the representative function it executed. -/
private lemma successful_physical_trace_refined_sample
    {n r cap k s c : ℕ} (G : SimpleGraph (Fin n))
    (A C Wfinal : Finset ℕ)
    (hA : A ⊆ Finset.range n)
    (hC : C.Nonempty) (hlarge : k < A.card)
    (hc : 0 < c)
    (hr : r = A.card / (4 * c ^ 2))
    (hcap : cap = A.card / (4 * c ^ 2 * (s + 1)))
    (choice : InitialChoice A C
      (fun b => numericNeighborhood G b ∩ A) r)
    (haccepted : (choice.exceptions k).card ≤ cap)
    (rep : ℕ → ℕ) (hrep : ∀ b ∈ C, choice.representative b = rep b)
    (order : List ℕ)
    (horder : order.toFinset = choice.exceptions k)
    (hnodup : order.Nodup)
    (trials : ∀ b : ℕ, List (LocalTrial
      (((numericNeighborhood G b ∩ A) \
        (numericNeighborhood G (rep b) ∩ A)) ∪
       ((numericNeighborhood G (rep b) ∩ A) \
        (numericNeighborhood G b ∩ A))) s))
    (hscan : phase3Scan (fun b => numericNeighborhood G b ∩ A)
      C rep k s trials order
      (phaseTwoSample G (choice.exceptions k) A choice.sample)
      (phaseTwoSample G (choice.exceptions k) A choice.sample) = some Wfinal) :
    Lax457868Proofs.RefinedSampleSpec.IsRefinedSample
      (neighborhoodFamily C (fun b => numericNeighborhood G b ∩ A))
      (A : Set ℕ) (Wfinal : Set ℕ)
      ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k := by
  classical
  let physical : InitialChoice A C
      (fun b => numericNeighborhood G b ∩ A) r := {
    choice with
    representative := rep
    representative_mem := by
      intro b hb
      rw [← hrep b hb]
      exact choice.representative_mem b hb
    representative_trace := by
      intro b hb
      rw [← hrep b hb]
      exact choice.representative_trace b hb
    representative_constant := by
      intro b hb b' hb' ht
      rw [← hrep b hb, ← hrep b' hb']
      exact choice.representative_constant b hb b' hb' ht
  }
  have hexceptions : physical.exceptions k = choice.exceptions k := by
    ext b
    simp only [InitialChoice.exceptions, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hfar⟩
      refine ⟨hb, ?_⟩
      simpa [physical, ← hrep b hb] using hfar
    · rintro ⟨hb, hfar⟩
      refine ⟨hb, ?_⟩
      simpa [physical, ← hrep b hb] using hfar
  have hsample : physical.sample = choice.sample := rfl
  apply successful_trace_refined_sample G A C Wfinal hA hC hlarge hc
    hr hcap physical (by simpa [hexceptions] using haccepted)
    order (by simpa [hexceptions] using horder) hnodup trials
  simpa only [hexceptions, hsample] using hscan

end

/-- The physical state preserved for another sampler round. Scratch lists are
tracked by their lengths; all five repair marks have been cleared. -/
def FinalFrame
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (_S : RuntimeInput R s repairCap) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "qpow" = Q ∧
  σ.arrs "activeA" = arrOf n (setFlag A) ∧
  σ.arrs "activeB" = arrOf n R.I.activeB ∧
  σ.arrs "off" = arrOf (n + 1) (offset x) ∧
  σ.arrs "tgt" = arrOf targetCap (target x) ∧
  (σ.arrs "drawDomain").length = n ∧
  (σ.arrs "key0").length = n ∧
  (σ.arrs "sampleDraws").length = bufferCap ∧
  σ.arrs "trialActive" = arrOf n (fun _ => 0) ∧
  σ.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
  σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
  σ.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
  σ.arrs "repairRMarks" = arrOf n (fun _ => 0) ∧
  (σ.arrs "trialRowList").length = n ∧
  (σ.arrs "trialDesiredList").length = n ∧
  (σ.arrs "trialDiffList").length = n ∧
  (σ.arrs "repairBList").length = n ∧
  (σ.arrs "repairRList").length = n

/-- The accepted branch retains the concrete initial choice, both checked
preparation orders, the phase-three trace, and both exact source charges. -/
def AcceptedExecution
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (_S : RuntimeInput R s repairCap)
    (τ σout : Env) (Wfinal : Finset ℕ)
    (consumed phaseCost partitionCost groupCost offsetCost
      repairCost : ℕ) : Prop :=
  ∃ choice : InitialChoice A (activeVertices n R.I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r,
  ∃ q : ℕ,
  ∃ L : LoopInput B n s t bufferCap targetCap q repairCap k
      (choice.exceptions k).card G x (choice.exceptions k)
      (activeVertices n R.I.activeB)
      (phaseTwoSample G (choice.exceptions k) A choice.sample)
      A (phaseTwoSample G (choice.exceptions k) A choice.sample),
  ∃ Lfinal : LoopInput B n s t bufferCap targetCap q repairCap k
      (choice.exceptions k).card G x (choice.exceptions k)
      (activeVertices n R.I.activeB)
      (phaseTwoSample G (choice.exceptions k) A choice.sample) A Wfinal,
  ∃ steps : List ExecutedException,
  ∃ initialPacked phaseTwoPacked : ℕ → ℕ,
    τ.vars "initialRetryStatus" = 1 ∧
    σout.vars "initialRetryStatus" = 1 ∧
    (choice.exceptions k).card ≤ initialCap ∧
    (∀ b ∈ activeVertices n R.I.activeB,
      choice.representative b = L.rep b) ∧
    phaseCost = exceptionPhaseCost x initialPacked n choice.sample.card targetCap ∧
    partitionCost = fullSamplePartitionCost x phaseTwoPacked n
      (phaseTwoSample G (choice.exceptions k) A choice.sample).card ∧
    groupCost = 20 * n + 9 +
      64 * ((activeVertices n R.I.activeB).card + Q + 1) ∧
    offsetCost = 18 * q + 8 ∧
    PrefixEnumerates choice.sample.card initialPacked choice.sample ∧
    PrefixEnumerates
      (phaseTwoSample G (choice.exceptions k) A choice.sample).card
      phaseTwoPacked
      (phaseTwoSample G (choice.exceptions k) A choice.sample) ∧
    L.σ.vars "qpow" = Q ∧
    Run B prepareRepairSource τ L.σ
      (phaseCost + partitionCost + groupCost + offsetCost + 2) ∧
    Run B exceptionRepairPackedSource L.σ σout
      (10 + traceRunCost x G A L.rep L.size L.label L.ord s k steps +
        (if Lfinal.σ.vars "repairRetryStatus" = 1 then 20 * n + 13 else 5)) ∧
    repairCost = 2 + (10 + traceRunCost x G A L.rep L.size L.label L.ord s k steps +
      (if Lfinal.σ.vars "repairRetryStatus" = 1 then 20 * n + 13 else 5)) ∧
    L.bits = R.I.bits.drop consumed ∧ L.rest = R.I.rest ∧
    (choice.exceptions k).card * (repairCap * (s * t * Nat.clog 2 n)) ≤
      L.bits.length ∧
    Lfinal.bits = L.bits.drop (traceBitCost G A L.rep steps) ∧
    SameFixed L Lfinal ∧
    steps.map ExecutedException.vertex =
      (Stack.toList (choice.exceptions k).card L.exceptionList).take steps.length ∧
    (∀ z ∈ steps, z.attempts ≤ repairCap ∧ z.used ≤ z.attempts * (s * t)) ∧
    σout.inp = Lfinal.bits.map Bool.toNat ++ L.rest ∧
    (∀ a, a ≠ "ord" → σout.arrs a = Lfinal.σ.arrs a) ∧
    (∀ v, v ≠ "sampleCount" → v ≠ "sampleCursor" →
      σout.vars v = Lfinal.σ.vars v)

private lemma finalFrame_of_run
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      cost : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    {σ : Env} (hrun : Run B completeSamplerSource R.I.σ σ cost)
    (hn : σ.vars "n" = n) (hqpow : σ.vars "qpow" = Q)
    (htrial : σ.arrs "trialActive" = arrOf n (fun _ => 0))
    (hrow : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hdesired : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0))
    (hBmarks : σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hRmarks : σ.arrs "repairRMarks" = arrOf n (fun _ => 0)) :
    FinalFrame R S σ := by
  have hlen (a : String) : (σ.arrs a).length = (R.I.σ.arrs a).length :=
    run_array_length_eq hrun a
  have harr {a : String} (ha : a ∉ completeSamplerSource.warrs) :
      σ.arrs a = R.I.σ.arrs a := hrun.frame_arr a ha
  refine ⟨hn, hqpow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htrial,
    hrow, hdesired, hBmarks, hRmarks, ?_, ?_, ?_, ?_, ?_⟩
  · rw [harr (by decide)]; exact R.hactiveA
  · rw [harr (by decide)]; exact R.I.hactiveB
  · rw [harr (by decide)]; exact R.I.hoff
  · rw [harr (by decide)]; exact R.I.htarget
  · rw [hlen, R.I.hdrawDomain]; simp [arrOf, S.hdomainCap]
  · rw [hlen, R.I.hkey0]; simp [arrOf]
  · rw [hlen, R.I.hsampleDraws]; simp [arrOf]
  · rw [hlen]; exact S.hrowLength
  · rw [hlen]; exact S.hdesiredLength
  · rw [hlen]; exact S.hdiffLength
  · rw [hlen]; exact S.hBListLength
  · rw [hlen]; exact S.hRListLength


/-- Execute the fixed full source. Initial and local capped failures remain
explicit statuses; the successful packed sample satisfies the mathematical
refined-sample contract. The execution charge is the sum of the checked
attempt charges, one guard, the five preparation charges, and the checked
phase-three charge. -/
lemma completeSamplerSource_run
    {B n m domainCap r t bufferCap targetCap Q k initialCap s repairCap
      attemptCap c : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (R : ReadyInput B n m domainCap r t bufferCap targetCap Q k initialCap G x A)
    (S : RuntimeInput R s repairCap)
    (hcapRegister : R.I.σ.vars "initialRetryCap" = attemptCap)
    (hcapB : attemptCap < B)
    (hbudget : attemptCap * attemptBitBudget n m r t +
      initialCap * (repairCap * (s * t * Nat.clog 2 n)) ≤ R.I.bits.length)
    (hC : (activeVertices n R.I.activeB).Nonempty)
    (hlarge : k < A.card)
    (hc : 0 < c)
    (hr : r = A.card / (4 * c ^ 2))
    (hinitialCap : initialCap = A.card / (4 * c ^ 2 * (s + 1))) :
    ∃ (σout : Env) (charges : List ℕ)
      (phaseCost partitionCost groupCost offsetCost repairCost : ℕ)
      (cost : ℕ),
      Run B completeSamplerSource R.I.σ σout cost ∧
      (∀ q ∈ charges, CheckedAttemptCharge B n m r t targetCap q) ∧
      charges.length ≤ attemptCap ∧
      cost = charges.sum + 28 * charges.length + 22 +
        (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size) +
        phaseCost + partitionCost + groupCost + offsetCost + repairCost ∧
      (∃ usedInitial usedRepair : ℕ,
        σout.inp = (R.I.bits.drop (usedInitial + usedRepair)).map Bool.toNat ++
          R.I.rest ∧
        usedInitial ≤ attemptCap * attemptBitBudget n m r t) ∧
      FinalFrame R S σout ∧
      ((∃ (W : Finset ℕ) (packed : ℕ → ℕ),
          σout.vars "repairRetryStatus" = 1 ∧
          σout.arrs "sampleFlags" = arrOf n (setFlag W) ∧
          σout.arrs "ord" = arrOf n packed ∧
          PrefixEnumerates (σout.vars "sampleCount") packed W ∧
          σout.vars "sampleCount" = W.card ∧
          Lax457868Proofs.RefinedSampleSpec.IsRefinedSample
            (neighborhoodFamily (activeVertices n R.I.activeB)
              (fun b => numericNeighborhood G b ∩ A))
            (A : Set ℕ) (W : Set ℕ)
            ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) k ∧
          (∃ τ : Env, ∃ consumed : ℕ,
            Run B initialSamplerRetriesSource R.I.σ τ
              (charges.sum + 28 * charges.length + 22) ∧
            τ.inp = (R.I.bits.drop consumed).map Bool.toNat ++ R.I.rest ∧
            consumed ≤ attemptCap * attemptBitBudget n m r t ∧
            AcceptedExecution R S τ σout W consumed phaseCost partitionCost
              groupCost offsetCost repairCost)) ∨
        (σout.vars "initialRetryStatus" = 2 ∨
          σout.vars "initialRetryStatus" = 3) ∨
        (σout.vars "repairRetryStatus" = 2 ∨
          σout.vars "repairRetryStatus" = 3)) := by
  classical
  have hinitBudget : attemptCap * attemptBitBudget n m r t ≤
      R.I.bits.length := by omega
  obtain ⟨τ, charges, consumed, rinitial, hchecked,
    hcharges, hconsumed, hinputInitial, hnInitial, hqInitial,
    houtcome⟩ := initialSamplerRetriesSource_run attemptCap R
      hcapRegister hcapB hinitBudget
  let initialCost := charges.sum + 28 * charges.length + 22
  let guard : Cond := .eq (.var "initialRetryStatus") (.lit 1)
  let guardCost := 1 + guard.size
  have hnPos : 0 < n := by
    obtain ⟨b, hb⟩ := hC
    exact Nat.pos_of_ne_zero (by
      intro hz
      have hbn := (mem_activeVertices.mp hb).1
      simp [hz] at hbn)
  have hBthree : 3 < B := by
    have := R.hnB
    omega
  have hfailedFrame {cost : ℕ}
      (hrun : Run B completeSamplerSource R.I.σ τ cost) :
      FinalFrame R S τ := by
    apply finalFrame_of_run R S hrun hnInitial hqInitial
    · rw [rinitial.frame_arr "trialActive" (by decide)]
      exact S.htrialZero
    · rw [rinitial.frame_arr "trialRowMarks" (by decide)]
      exact S.hrowZero
    · rw [rinitial.frame_arr "trialDesiredMarks" (by decide)]
      exact S.hdesiredZero
    · rw [rinitial.frame_arr "repairBMarks" (by decide)]
      exact S.hBMarksZero
    · rw [rinitial.frame_arr "repairRMarks" (by decide)]
      exact S.hRMarksZero
  rcases houtcome with haccepted | hdrawFailure | hexhausted
  · let bits := R.I.bits.drop consumed
    obtain ⟨choice, q, L, phaseCost, partitionCost, groupCost,
      offsetCost, initialPacked, phaseTwoPacked, rprep, hphaseCost,
      hpartitionCost, hgroupCost, hoffsetCost, hinitialPrefix,
      hphaseTwoPrefix, hLqpow, hLbits, hLrest, hstatus, hcapChoice,
      hrepChoice, _hprepBound⟩ :=
      accepted_preparation_run R S rinitial hnInitial hqInitial bits
        hinputInitial haccepted
    have hrepairBudget :
        (choice.exceptions k).card *
          (repairCap * (s * t * Nat.clog 2 n)) ≤ L.bits.length := by
      rw [hLbits]
      have hle := Nat.mul_le_mul_right
        (repairCap * (s * t * Nat.clog 2 n)) hcapChoice
      simp only [bits, List.length_drop]
      omega
    obtain ⟨Wfinal, Lfinal, steps, σout, rrepair,
      hbitsFinal, hfixed, hsteps, hvalid, hinputOut,
      hrepairOutcome⟩ := exceptionRepairPacked_run L hrepairBudget
    let repairCost := 10 + traceRunCost x G A L.rep L.size L.label L.ord s k steps +
      (if Lfinal.σ.vars "repairRetryStatus" = 1 then 20 * n + 13 else 5)
    let prepCost := phaseCost + partitionCost + groupCost + offsetCost + 2
    have hguard : guard.evalB B τ = some true := by
      have hstatusB : τ.vars "initialRetryStatus" < B := by
        rw [hstatus]
        omega
      simpa [guard, hstatus] using evalB_condEq
        (evalB_var hstatusB)
        (evalB_lit (by omega : 1 < B))
    have rtail : Run B completeSamplerTail τ σout (prepCost + repairCost) := by
      simpa [completeSamplerTail, prepCost, repairCost] using rprep.seq rrepair
    have rwhole : Run B completeSamplerSource R.I.σ σout
        (initialCost + (guardCost + (prepCost + repairCost))) := by
      have h := rinitial.seq
        (Run.ite_true (d := .skip) hguard rtail)
      simpa [completeSamplerSource, guard, guardCost, initialCost] using h
    have hcost : initialCost + (guardCost + (prepCost + repairCost)) =
        charges.sum + 28 * charges.length + 22 +
          (1 + (Cond.eq (.var "initialRetryStatus") (.lit 1)).size) +
          phaseCost + partitionCost + groupCost + offsetCost +
          (2 + repairCost) := by
      simp [initialCost, guardCost, guard, prepCost]
      omega
    have hmarksOut :
        σout.arrs "trialActive" = arrOf n (fun _ => 0) ∧
        σout.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
        σout.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
        σout.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
        σout.arrs "repairRMarks" = arrOf n (fun _ => 0) := by
      rcases hrepairOutcome with hsuccess | hfailure
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, harrFrame, _,
          _, _, _⟩ := hsuccess
        exact ⟨(harrFrame "trialActive" (by decide)).trans Lfinal.htrialZero,
          (harrFrame "trialRowMarks" (by decide)).trans Lfinal.hrowZero,
          (harrFrame "trialDesiredMarks" (by decide)).trans Lfinal.hdesiredZero,
          (harrFrame "repairBMarks" (by decide)).trans Lfinal.hBMarksZero,
          (harrFrame "repairRMarks" (by decide)).trans Lfinal.hRMarksZero⟩
      · obtain ⟨_, _, heq⟩ := hfailure
        subst σout
        exact ⟨Lfinal.htrialZero, Lfinal.hrowZero, Lfinal.hdesiredZero,
          Lfinal.hBMarksZero, Lfinal.hRMarksZero⟩
    have hnOut : σout.vars "n" = n := by
      rcases hrepairOutcome with hsuccess | hfailure
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hvarFrame,
          _, _, _⟩ := hsuccess
        rw [hvarFrame "n" (by decide) (by decide)]
        exact Lfinal.hn
      · obtain ⟨_, _, heq⟩ := hfailure
        rw [heq]
        exact Lfinal.hn
    have hqFinal : Lfinal.σ.vars "qpow" = Q :=
      hfixed.qpow.trans hLqpow
    have hqOut : σout.vars "qpow" = Q := by
      rcases hrepairOutcome with hsuccess | hfailure
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hvarFrame,
          _, _, _⟩ := hsuccess
        rw [hvarFrame "qpow" (by decide) (by decide)]
        exact hqFinal
      · obtain ⟨_, _, heq⟩ := hfailure
        rw [heq]
        exact hqFinal
    have hframe : FinalFrame R S σout :=
      finalFrame_of_run R S rwhole hnOut hqOut hmarksOut.1
        hmarksOut.2.1 hmarksOut.2.2.1 hmarksOut.2.2.2.1
        hmarksOut.2.2.2.2
    refine ⟨σout, charges, phaseCost, partitionCost, groupCost,
      offsetCost, 2 + repairCost,
      initialCost + (guardCost + (prepCost + repairCost)),
      rwhole, hchecked, hcharges, hcost, ?_, hframe, ?_⟩
    · refine ⟨consumed, traceBitCost G A L.rep steps, ?_, hconsumed⟩
      simpa [hinputOut, hbitsFinal, hLbits, hLrest, bits,
        List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rcases hrepairOutcome with hsuccess | hfailure
    · obtain ⟨hrepairStatus, _hindex, _hstepsLen,
        packed, trials, hsample, hord, hprefix, hcount,
        _hcursor, harrFrame, hvarFrame, _houtFrame,
        hscan, _hcard⟩ := hsuccess
      have hrepairStatusOut : σout.vars "repairRetryStatus" = 1 := by
        rw [hvarFrame "repairRetryStatus" (by decide) (by decide)]
        exact hrepairStatus
      have horderSet :
          (Stack.toList (choice.exceptions k).card L.exceptionList).toFinset =
            choice.exceptions k := by
        ext b
        simpa using L.hprefix.2 b
      have hcontract := successful_physical_trace_refined_sample
        G A (activeVertices n R.I.activeB) Wfinal R.I.hA hC hlarge
        hc hr hinitialCap choice hcapChoice L.rep hrepChoice
        (Stack.toList (choice.exceptions k).card L.exceptionList)
        horderSet L.hprefix.1 trials hscan
      have hstatusOut : σout.vars "initialRetryStatus" = 1 := by
        rw [rrepair.frame_var "initialRetryStatus" (by decide)]
        rw [rprep.frame_var "initialRetryStatus" (by decide)]
        exact hstatus
      have hexecution : AcceptedExecution R S τ σout Wfinal consumed phaseCost
          partitionCost groupCost offsetCost (2 + repairCost) := by
        refine ⟨choice, q, L, Lfinal, steps,
          initialPacked, phaseTwoPacked, hstatus, hstatusOut,
          hcapChoice, hrepChoice, hphaseCost, hpartitionCost,
          hgroupCost, hoffsetCost, hinitialPrefix, hphaseTwoPrefix,
          hLqpow, rprep, ?_, ?_, hLbits, hLrest, hrepairBudget,
          hbitsFinal, hfixed, hsteps, hvalid, hinputOut,
          ?_, ?_⟩
        · simpa [repairCost] using rrepair
        · rfl
        · exact harrFrame
        · exact hvarFrame
      exact Or.inl ⟨Wfinal, packed, hrepairStatusOut,
        hsample, hord, hprefix, hcount,
        hcontract, τ, consumed, rinitial, hinputInitial,
        hconsumed, hexecution⟩
    · rcases hfailure with ⟨hstatusRepair, _hindex, heq⟩
      exact Or.inr (Or.inr (by simpa [heq] using hstatusRepair))
  · obtain ⟨hstatus, _hfailureKind⟩ := hdrawFailure
    have hguard : guard.evalB B τ = some false := by
      have hstatusB : τ.vars "initialRetryStatus" < B := by
        rw [hstatus]
        omega
      simpa [guard, hstatus] using evalB_condEq
        (evalB_var hstatusB)
        (evalB_lit (by omega : 1 < B))
    have rwhole : Run B completeSamplerSource R.I.σ τ
        (initialCost + guardCost + 1) := by
      have h := rinitial.seq
        (Run.ite_false (c := completeSamplerTail) hguard Run.skip)
      simpa [completeSamplerSource, guard, guardCost, initialCost,
        Nat.add_assoc] using h
    refine ⟨τ, charges, 0, 0, 0, 0, 1, initialCost + guardCost + 1,
      rwhole, hchecked, hcharges, ?_, ?_, hfailedFrame rwhole,
      Or.inr (Or.inl (Or.inl hstatus))⟩
    · simp [initialCost, guardCost, guard]
    · refine ⟨consumed, 0, ?_, hconsumed⟩
      simpa using hinputInitial
  · obtain ⟨hstatus, _hlen⟩ := hexhausted
    have hguard : guard.evalB B τ = some false := by
      have hstatusB : τ.vars "initialRetryStatus" < B := by
        rw [hstatus]
        omega
      simpa [guard, hstatus] using evalB_condEq
        (evalB_var hstatusB)
        (evalB_lit (by omega : 1 < B))
    have rwhole : Run B completeSamplerSource R.I.σ τ
        (initialCost + guardCost + 1) := by
      have h := rinitial.seq
        (Run.ite_false (c := completeSamplerTail) hguard Run.skip)
      simpa [completeSamplerSource, guard, guardCost, initialCost,
        Nat.add_assoc] using h
    refine ⟨τ, charges, 0, 0, 0, 0, 1, initialCost + guardCost + 1,
      rwhole, hchecked, hcharges, ?_, ?_, hfailedFrame rwhole,
      Or.inr (Or.inl (Or.inr hstatus))⟩
    · simp [initialCost, guardCost, guard]
    · refine ⟨consumed, 0, ?_, hconsumed⟩
      simpa using hinputInitial

end Lax457868Proofs.CompleteSamplerSource
