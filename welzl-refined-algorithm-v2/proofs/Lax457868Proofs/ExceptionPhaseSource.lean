import Lax457868Proofs.ExceptionRefinementScan
import Lax457868Proofs.SamplePacking
import Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource
import Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource

/-! Initialize the exception trace partition on the packed initial sample,
scan the active side, and pack the enlarged sample. -/

namespace Lax457868Proofs.ExceptionPhaseSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding Lax11Proofs.CC
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerRefinementBudget
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionRefinementScan
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax457868Proofs.ReusedOriginal.Construction.PartitionLoopSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionRefinement
open Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

noncomputable section

/-- Numeric graph neighborhoods, with the candidate index in the first
argument of `Adjn`, matching the CSR scan direction. -/
def numericNeighborhood {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range n).filter fun i => Adjn G i b

private lemma numericNeighborhood_mem {n : ℕ} (G : SimpleGraph (Fin n))
    {i b : ℕ} (hi : i < n) :
    i ∈ numericNeighborhood G b ↔ Adjn G i b := by
  simp [numericNeighborhood, hi]

private lemma adjn_fin_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (i b : Fin n) : Adjn G i.val b.val ↔ G.Adj i b := by
  simp only [Adjn]
  constructor
  · rintro ⟨hi, hb, hadj⟩
    simpa using hadj
  · intro hadj
    exact ⟨i.isLt, b.isLt, hadj⟩

private lemma numeric_trace_iff {n : ℕ} (G : SimpleGraph (Fin n))
    {W : Finset ℕ} (hW : W ⊆ Finset.range n)
    (b b' : Fin n) :
    (neighborhoodTrace G (finSetAsSet W) b =
        neighborhoodTrace G (finSetAsSet W) b') ↔
      trace (numericNeighborhood G) W b.val =
        trace (numericNeighborhood G) W b'.val := by
  constructor <;> intro h
  · apply Finset.ext
    intro i
    by_cases hiW : i ∈ W
    · have hi : i < n := Finset.mem_range.mp (hW hiW)
      have heq := Set.ext_iff.mp h ⟨i, hi⟩
      simpa [trace, numericNeighborhood_mem G hi, neighborhoodTrace,
        finSetAsSet, hiW, adjn_fin_iff G ⟨i, hi⟩ b,
        adjn_fin_iff G ⟨i, hi⟩ b', G.adj_comm] using heq
    · simp [trace, hiW]
  · apply Set.ext
    intro i
    by_cases hiW : i.val ∈ W
    · have heq := congrArg (fun S : Finset ℕ => i.val ∈ S) h
      simpa [trace, numericNeighborhood_mem G i.isLt, neighborhoodTrace,
        finSetAsSet, hiW, adjn_fin_iff G i b,
        adjn_fin_iff G i b', G.adj_comm] using heq
    · simp [neighborhoodTrace, finSetAsSet, hiW]

private lemma numeric_CSR {n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} (hx : EncodesGraph x n G)
    {A E : Finset ℕ} (hA : A ⊆ Finset.range n) :
    ∀ i ∈ A, ∀ b ∈ E,
      (b ∈ activeTargets (target x) (setFlag E)
        (offset x i) (offset x (i + 1)) ↔
          i ∈ numericNeighborhood G b) := by
  intro i hi b hb
  have hin : i < n := Finset.mem_range.mp (hA hi)
  rw [mem_activeTargets_block hx hin, numericNeighborhood_mem G hin]
  simp [setFlag, hb]

/-- The branch is selected by the actual packed exception count. -/
def exceptionPhase : Com :=
  .ite (.eq (.var "exceptionCount") (.lit 0))
    packMarkedSamples
    (seqs [partitionRefinePrefix "exceptionFlags" "ord" "sampleCount" "classB",
      exceptionRefinementScan, packMarkedSamples])

def phaseTwoSample {n : ℕ} (G : SimpleGraph (Fin n))
    (E A W : Finset ℕ) : Finset ℕ :=
  phase2Scan (numericNeighborhood G) E
    ((List.range n).filter fun a => a ∈ A) W

def exceptionPhaseCost (x : List ℕ) (ord : ℕ → ℕ)
    (n sampleCount targetCap : ℕ) : ℕ :=
  1 + (Cond.eq (.var "exceptionCount") (.lit 0)).size +
    (60 * (n + 1) + 2 +
      (324 * refinementWork x ord 0 sampleCount + 4)) +
    339 * (n + targetCap + 1) + (20 * n + 9)

private lemma phase2Scan_empty (N : ℕ → Finset ℕ)
    (as : List ℕ) (W : Finset ℕ) : phase2Scan N ∅ as W = W := by
  induction as generalizing W with
  | nil => rfl
  | cons a as ih =>
      simpa [phase2Scan, phase2Step, splitsExceptionPairB] using ih W

private lemma phase2Scan_range {n : ℕ} (N : ℕ → Finset ℕ)
    (E W : Finset ℕ) (as : List ℕ)
    (hW : W ⊆ Finset.range n)
    (has : ∀ a ∈ as, a < n) :
    phase2Scan N E as W ⊆ Finset.range n := by
  induction as generalizing W with
  | nil => simpa [phase2Scan] using hW
  | cons a as ih =>
      have ha : a < n := has a (by simp)
      have hstep : phase2Step N E W a ⊆ Finset.range n := by
        intro v hv
        simp only [phase2Step] at hv
        split_ifs at hv
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact Finset.mem_range.mpr ha
          · exact hW hv
        · exact hW hv
      simpa [phase2Scan] using ih (phase2Step N E W a) hstep
        (by intro v hv; exact has v (by simp [hv]))

private lemma flagged_setFlag {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) :
    flaggedVertices n (setFlag S) = S := by
  ext v
  simp only [flaggedVertices, mem_activeVertices, setFlag]
  constructor
  · rintro ⟨_, h⟩
    by_cases hv : v ∈ S <;> simp [hv] at h ⊢
  · intro hv
    exact ⟨Finset.mem_range.mp (hS hv), by simp [hv]⟩

/-- The concrete state needed to initialize and scan an already packed sample.
The input carries the arrays and capacities, but no exception classification. -/
structure Input (B n targetCap sampleCount : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ)
    (A E W : Finset ℕ) where
  σ : Env
  activeB : ℕ → ℕ
  ord : ℕ → ℕ
  classB : ℕ → ℕ
  classSize : ℕ → ℕ
  markedCount : ℕ → ℕ
  stamp : ℕ → ℕ
  marked : ℕ → ℕ
  touched : ℕ → ℕ
  split : ℕ → ℕ
  repB : ℕ → ℕ
  hx : EncodesGraph x n G
  htargetCap : targetCap = 2 * edgeCount x
  hn : σ.vars "n" = n
  hsampleCount : σ.vars "sampleCount" = sampleCount
  hexceptionCount : σ.vars "exceptionCount" = E.card
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htarget : σ.arrs "tgt" = arrOf targetCap (target x)
  hactiveA : σ.arrs "activeA" = arrOf n (setFlag A)
  hactiveB : σ.arrs "activeB" = arrOf n activeB
  hactiveE : σ.arrs "exceptionFlags" = arrOf n (setFlag E)
  hsampleFlags : σ.arrs "sampleFlags" = arrOf n (setFlag W)
  hord : σ.arrs "ord" = arrOf n ord
  hclassB : σ.arrs "classB" = arrOf n classB
  hclassSize : σ.arrs "classSize" = arrOf n classSize
  hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount
  hstamp : σ.arrs "stamp" = arrOf n stamp
  hmarked : σ.arrs "marked" = arrOf n marked
  htouched : σ.arrs "touched" = arrOf n touched
  hsplit : σ.arrs "split" = arrOf n split
  hrepB : σ.arrs "repB" = arrOf n repB
  henum : PrefixEnumerates sampleCount ord W
  hA : A ⊆ Finset.range n
  hE : E ⊆ Finset.range n
  hW : W ⊆ Finset.range n
  hWA : W ⊆ A
  hsampleCountN : sampleCount ≤ n
  hnB : n < B
  htargetCapB : targetCap < B
  honeB : 1 < B

private lemma Input.refinePrefix_run {B n targetCap sampleCount : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A E W : Finset ℕ}
    (I : Input B n targetCap sampleCount G x A E W)
    (hEne : E.Nonempty) :
    ∃ σ₁, Run B
        (partitionRefinePrefix "exceptionFlags" "ord" "sampleCount" "classB")
        I.σ σ₁
        (60 * (n + 1) + 2 +
          (324 * refinementWork x I.ord 0 sampleCount + 4)) ∧
      RefineTestsInv G x targetCap sampleCount
        "exceptionFlags" "ord" "sampleCount" "classB"
        (setFlag E) I.ord σ₁ ∧
      σ₁.vars "ti" = sampleCount := by
  have hnonempty : (activeVertices n (setFlag E)).Nonempty := by
    obtain ⟨b, hb⟩ := hEne
    refine ⟨b, mem_activeVertices.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_range.mp (I.hE hb)
    · simp [setFlag, hb]
  have hrange := PrefixEnumerates.entry_lt I.henum
    (fun v hv => Finset.mem_range.mp (I.hW hv))
  have hbound : ∀ v < n, setFlag E v < B := by
    intro v hv
    have honeB := I.honeB
    by_cases hvE : v ∈ E <;> simp [setFlag, hvE] <;> omega
  apply partitionRefinePrefix_run
    (activeName := "exceptionFlags") (testsName := "ord")
    (testCountName := "sampleCount") (clsName := "classB")
    I.hx I.htargetCap I.hn I.hsampleCount I.hoff I.htarget
    I.hactiveE I.hord I.hclassB I.hclassSize I.hmarkedCount
    I.hstamp I.hmarked I.htouched I.hsplit
    hnonempty I.hsampleCountN hrange I.hnB I.htargetCapB I.honeB hbound
  all_goals decide

/-- Run the fixed phase-two source on the already packed initial sample.
The exception partition is created by the original prefix routine; the scan
receives its classification as a derived fact. -/
lemma exceptionPhase_run {B n targetCap sampleCount : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A E W : Finset ℕ}
    (I : Input B n targetCap sampleCount G x A E W) :
    ∃ σ' packed finalLabel finalSize,
      Run B exceptionPhase I.σ σ'
        (exceptionPhaseCost x I.ord n sampleCount targetCap) ∧
      σ'.arrs "sampleFlags" =
        arrOf n (setFlag (phaseTwoSample G E A W)) ∧
      σ'.arrs "ord" = arrOf n packed ∧
      PrefixEnumerates (σ'.vars "sampleCount") packed
        (phaseTwoSample G E A W) ∧
      σ'.vars "sampleCount" = (phaseTwoSample G E A W).card ∧
      σ'.arrs "classB" = arrOf n finalLabel ∧
      σ'.arrs "classSize" = arrOf n finalSize ∧
      (E.Nonempty →
        ClassSizes n (σ'.vars "classCount") (setFlag E)
          finalLabel finalSize ∧
        LabelsOccupyPrefix (σ'.vars "classCount") finalLabel E ∧
        ∀ b ∈ E, ∀ b' ∈ E,
          (finalLabel b = finalLabel b' ↔
            trace (numericNeighborhood G) (phaseTwoSample G E A W) b =
              trace (numericNeighborhood G) (phaseTwoSample G E A W) b')) ∧
      σ'.arrs "activeA" = arrOf n (setFlag A) ∧
      σ'.arrs "exceptionFlags" = arrOf n (setFlag E) ∧
      σ'.arrs "activeB" = arrOf n I.activeB ∧
      σ'.arrs "repB" = arrOf n I.repB ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.vars "n" = n ∧
      σ'.vars "exceptionCount" = E.card ∧
      σ'.inp = I.σ.inp ∧ σ'.out = I.σ.out ∧
      (∀ a, a ∉ exceptionPhase.warrs → σ'.arrs a = I.σ.arrs a) ∧
      (∀ v, v ∉ exceptionPhase.wvars → σ'.vars v = I.σ.vars v) := by
  have hSampleRange : phaseTwoSample G E A W ⊆ Finset.range n := by
    unfold phaseTwoSample
    apply phase2Scan_range (numericNeighborhood G) E W
      ((List.range n).filter fun a => a ∈ A) I.hW
    intro a ha
    have haA : a ∈ A := by simpa using (List.mem_filter.mp ha).2
    exact Finset.mem_range.mp (I.hA haA)
  have hFlagged : flaggedVertices n
      (setFlag (phaseTwoSample G E A W)) = phaseTwoSample G E A W :=
    flagged_setFlag hSampleRange
  have hFlags01 : ∀ v < n, setFlag (phaseTwoSample G E A W) v ≤ 1 := by
    intro v hv
    by_cases h : v ∈ phaseTwoSample G E A W <;> simp [setFlag, h]
  by_cases hEne : E.Nonempty
  · obtain ⟨σ₁, rprefix, hI₁, hti⟩ := I.refinePrefix_run hEne
    rcases hI₁ with ⟨current₁, label₁, size₁, stamp₁, counts₁,
      marked₁, touched₁, split₁, _htiLe, _hcountLe,
      _hsampleCount₁, hn₁, hcurrent₁, hcurrentLe₁,
      hoff₁, htarget₁, hactiveE₁, hord₁,
      hclassB₁, hsize₁, hstamp₁, hcounts₁,
      hmarked₁, htouched₁, hsplit₁, _hstampLe₁,
      hcountsZero₁, hsizes₁, hoccupied₁, hclassifies₁⟩
    have hclassify₁ : ∀ b ∈ E, ∀ b' ∈ E,
        (label₁ b = label₁ b' ↔
          trace (numericNeighborhood G) W b =
            trace (numericNeighborhood G) W b') := by
      intro b hb b' hb'
      have hbN : b < n := Finset.mem_range.mp (I.hE hb)
      have hb'N : b' < n := Finset.mem_range.mp (I.hE hb')
      have hclass := hclassifies₁
        (u := (⟨b, hbN⟩ : Fin n))
        (by simp [setFlag, hb])
        (v := (⟨b', hb'N⟩ : Fin n))
        (by simp [setFlag, hb'])
      rw [hti, testPrefix_eq_finSetAsSet_of_prefixEnumerates I.henum] at hclass
      exact hclass.trans (numeric_trace_iff G I.hW ⟨b, hbN⟩ ⟨b', hb'N⟩)
    have hoccupiedE : LabelsOccupyPrefix current₁ label₁ E := by
      change LabelsOccupyPrefix current₁ label₁
        (flaggedVertices n (setFlag E)) at hoccupied₁
      rwa [flagged_setFlag I.hE] at hoccupied₁
    have hoffMono : ∀ i < n, offset x i ≤ offset x (i + 1) := by
      intro i hi
      exact I.hx.offset_mono i hi
    have hoffRange : ∀ i < n + 1, offset x i ≤ targetCap := by
      intro i hi
      rw [I.htargetCap]
      exact offset_le I.hx (by omega)
    have htargetRange : ∀ i < n, ∀ j,
        offset x i ≤ j → j < offset x (i + 1) → target x j < n := by
      intro i hi j _ hj
      exact target_lt' I.hx hi hj
    have hsample₁ : σ₁.arrs "sampleFlags" = arrOf n (setFlag W) :=
      (rprefix.frame_arr "sampleFlags" (by decide)).trans I.hsampleFlags
    have hactiveA₁ : σ₁.arrs "activeA" = arrOf n (setFlag A) :=
      (rprefix.frame_arr "activeA" (by decide)).trans I.hactiveA
    obtain ⟨σ₂, current₂, label₂, size₂, stamp₂, counts₂,
      marked₂, touched₂, split₂,
      _rscanExact, rscan, _hcursor₂, hn₂, hcurrent₂,
      _hcurrentLe₂, _hoff₂, _htarget₂, _hactiveA₂,
      _hactiveE₂, hsample₂, hlabel₂, hsize₂, _hstamp₂,
      _hcounts₂, _hmarked₂, _htouched₂, _hsplit₂,
      _hstampLe₂, _hcountsZero₂, hsizes₂,
      hoccupied₂, hclassify₂, _hinp₂, _hout₂,
      _harrayFrame₂, _hvarFrame₂⟩ :=
      exceptionRefinementScan_run I.hE I.hA I.hW
        hclassify₁ (numeric_CSR I.hx I.hA)
        hn₁ hcurrent₁ hoff₁ htarget₁ hactiveA₁ hactiveE₁
        hsample₁ hclassB₁ hsize₁ hstamp₁ hcounts₁
        hmarked₁ htouched₁ hsplit₁ hcurrentLe₁
        hoffMono hoffRange htargetRange
        I.hnB I.htargetCapB I.honeB hcountsZero₁
        hsizes₁ hoccupiedE
    have hord₂ : σ₂.arrs "ord" = arrOf n I.ord :=
      (rscan.frame_arr "ord" (by decide)).trans hord₁
    obtain ⟨σ₃, packed, rpack, hsample₃, hord₃,
      henum₃, hcount₃, _hcursor₃, _harrFrame₃,
      _hvarFrame₃, _hinp₃, _hout₃⟩ :=
      packMarkedSamples_run hn₂ hsample₂ hord₂
        hFlags01 I.hnB I.honeB
    have hrun : Run B exceptionPhase I.σ σ₃
        (exceptionPhaseCost x I.ord n sampleCount targetCap) := by
      have hcond : (Cond.eq (.var "exceptionCount") (.lit 0)).evalB B I.σ =
          some false := by
        have hEcard : E.card < B := by
          have hle := Finset.card_le_card I.hE
          simpa using lt_of_le_of_lt (by simpa using hle) I.hnB
        have hvar : (Expr.var "exceptionCount").evalB B I.σ = some E.card := by
          rw [evalB_var_iff]
          exact ⟨I.hexceptionCount.symm, by rw [I.hexceptionCount]; exact hEcard⟩
        have hzero : (Expr.lit 0).evalB B I.σ = some 0 := evalB_lit (by omega)
        have heval := evalB_condEq hvar hzero
        have hpos : E.card ≠ 0 := Finset.card_ne_zero.mpr hEne
        simpa [hpos] using heval
      have hseq := Run.seq rprefix (Run.seq rscan rpack)
      have hbranch : Run B
          (seqs [partitionRefinePrefix "exceptionFlags" "ord" "sampleCount" "classB",
            exceptionRefinementScan, packMarkedSamples]) I.σ σ₃
          (60 * (n + 1) + 2 +
            (324 * refinementWork x I.ord 0 sampleCount + 4) +
            (339 * (n + targetCap + 1) + (20 * n + 9))) := by
        simpa [seqs] using hseq
      simpa [exceptionPhase, exceptionPhaseCost, Nat.add_assoc] using
        (Run.ite_false (c := packMarkedSamples) hcond hbranch)
    refine ⟨σ₃, packed, label₂, size₂, hrun, ?_, hord₃, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [phaseTwoSample] using hsample₃
    · change PrefixEnumerates (σ₃.vars "sampleCount") packed
        (flaggedVertices n (setFlag (phaseTwoSample G E A W))) at henum₃
      rwa [hFlagged] at henum₃
    · change σ₃.vars "sampleCount" =
        (flaggedVertices n (setFlag (phaseTwoSample G E A W))).card at hcount₃
      rwa [hFlagged] at hcount₃
    · exact (rpack.frame_arr "classB" (by decide)).trans hlabel₂
    · exact (rpack.frame_arr "classSize" (by decide)).trans hsize₂
    · intro _
      have hcountClass : σ₃.vars "classCount" = current₂ := by
        rw [rpack.frame_var "classCount" (by decide)]
        exact hcurrent₂
      rw [hcountClass]
      exact ⟨hsizes₂, hoccupied₂, by simpa [phaseTwoSample] using hclassify₂⟩
    · exact (hrun.frame_arr "activeA" (by decide)).trans I.hactiveA
    · exact (hrun.frame_arr "exceptionFlags" (by decide)).trans I.hactiveE
    · exact (hrun.frame_arr "activeB" (by decide)).trans I.hactiveB
    · exact (hrun.frame_arr "repB" (by decide)).trans I.hrepB
    · exact (hrun.frame_arr "off" (by decide)).trans I.hoff
    · exact (hrun.frame_arr "tgt" (by decide)).trans I.htarget
    · exact (hrun.frame_var "n" (by decide)).trans I.hn
    · exact (hrun.frame_var "exceptionCount" (by decide)).trans I.hexceptionCount
    · exact hrun.frame_inp (by decide)
    · exact hrun.out_eq (by decide)
    · intro a ha; exact hrun.frame_arr a ha
    · intro v hv; exact hrun.frame_var v hv

  · have hEempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEne
    have hSampleEmpty : phaseTwoSample G E A W = W := by
      simp [phaseTwoSample, hEempty, phase2Scan_empty]
    have hFlags01W : ∀ v < n, setFlag W v ≤ 1 := by
      simpa [hSampleEmpty] using hFlags01
    obtain ⟨σ₃, packed, rpack, hsample₃, hord₃,
      henum₃, hcount₃, _hcursor₃, _harrFrame₃,
      _hvarFrame₃, _hinp₃, _hout₃⟩ :=
      packMarkedSamples_run I.hn I.hsampleFlags I.hord
        hFlags01W I.hnB I.honeB
    have hrun : Run B exceptionPhase I.σ σ₃
        (exceptionPhaseCost x I.ord n sampleCount targetCap) := by
      have hcond : (Cond.eq (.var "exceptionCount") (.lit 0)).evalB B I.σ =
          some true := by
        have hvar : (Expr.var "exceptionCount").evalB B I.σ = some 0 := by
          rw [evalB_var_iff]
          exact ⟨by rw [I.hexceptionCount, hEempty]; simp,
            by rw [I.hexceptionCount, hEempty]; simp only [Finset.card_empty];
               have := I.honeB; omega⟩
        have hzero : (Expr.lit 0).evalB B I.σ = some 0 :=
          evalB_lit (by have := I.honeB; omega)
        simpa using evalB_condEq hvar hzero
      have hshort : Run B exceptionPhase I.σ σ₃
          (1 + (Cond.eq (.var "exceptionCount") (.lit 0)).size +
            (20 * n + 9)) := by
        simpa [exceptionPhase] using
          (Run.ite_true (d := seqs [
            partitionRefinePrefix "exceptionFlags" "ord" "sampleCount" "classB",
            exceptionRefinementScan, packMarkedSamples]) hcond rpack)
      exact hshort.mono (by unfold exceptionPhaseCost; omega)
    refine ⟨σ₃, packed, I.classB, I.classSize, hrun, ?_, hord₃,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hSampleEmpty] using hsample₃
    · have henum₃' : PrefixEnumerates (σ₃.vars "sampleCount") packed
          (flaggedVertices n (setFlag (phaseTwoSample G E A W))) := by
        simpa [hSampleEmpty] using henum₃
      rwa [hFlagged] at henum₃'
    · have hcount₃' : σ₃.vars "sampleCount" =
          (flaggedVertices n (setFlag (phaseTwoSample G E A W))).card := by
        simpa [hSampleEmpty] using hcount₃
      rwa [hFlagged] at hcount₃'
    · exact (rpack.frame_arr "classB" (by decide)).trans I.hclassB
    · exact (rpack.frame_arr "classSize" (by decide)).trans I.hclassSize
    · intro h; exact (hEne h).elim
    · exact (hrun.frame_arr "activeA" (by decide)).trans I.hactiveA
    · exact (hrun.frame_arr "exceptionFlags" (by decide)).trans I.hactiveE
    · exact (hrun.frame_arr "activeB" (by decide)).trans I.hactiveB
    · exact (hrun.frame_arr "repB" (by decide)).trans I.hrepB
    · exact (hrun.frame_arr "off" (by decide)).trans I.hoff
    · exact (hrun.frame_arr "tgt" (by decide)).trans I.htarget
    · exact (hrun.frame_var "n" (by decide)).trans I.hn
    · exact (hrun.frame_var "exceptionCount" (by decide)).trans I.hexceptionCount
    · exact hrun.frame_inp (by decide)
    · exact hrun.out_eq (by decide)
    · intro a ha; exact hrun.frame_arr a ha
    · intro v hv; exact hrun.frame_var v hv

/-- The old duplicate-free test-prefix work bound makes the assembled source
cost linear in the graph's CSR capacity, vertex count, and sample count. -/
lemma Input.exceptionPhaseCost_le_linear {B n targetCap sampleCount : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A E W : Finset ℕ}
    (I : Input B n targetCap sampleCount G x A E W) :
    exceptionPhaseCost x I.ord n sampleCount targetCap ≤
      1 + (Cond.eq (.var "exceptionCount") (.lit 0)).size +
        (60 * (n + 1) + 2 +
          (324 * (targetCap + sampleCount) + 4)) +
        339 * (n + targetCap + 1) + (20 * n + 9) := by
  have hrange := PrefixEnumerates.entry_lt I.henum
    (fun v hv => Finset.mem_range.mp (I.hW hv))
  have hwork := refinementWork_le_edgeCount_add I.hx hrange
    I.henum.injective_on_prefix
  unfold exceptionPhaseCost
  rw [← I.htargetCap] at hwork
  omega

/-- Phase two keeps the packed initial sample. -/
lemma phaseTwoSample_contains {n : ℕ} (G : SimpleGraph (Fin n))
    (E A W : Finset ℕ) : W ⊆ phaseTwoSample G E A W := by
  exact phase2Scan_mono (numericNeighborhood G) E
    ((List.range n).filter fun a => a ∈ A) W

/-- Every added sample vertex is charged to a new exception trace class. -/
lemma phaseTwoSample_card_le {n : ℕ} (G : SimpleGraph (Fin n))
    (E A W : Finset ℕ) :
    (phaseTwoSample G E A W).card ≤ W.card + E.card := by
  exact phase2Scan_card_add_le (numericNeighborhood G) E
    ((List.range n).filter fun a => a ∈ A) W

/-- Equal final exception traces agree on every scanned active vertex. -/
lemma phaseTwoSample_separates {n : ℕ} (G : SimpleGraph (Fin n))
    (E A W : Finset ℕ) (hA : A ⊆ Finset.range n)
    (b b' : ℕ) (hb : b ∈ E) (hb' : b' ∈ E)
    (htrace : trace (numericNeighborhood G) (phaseTwoSample G E A W) b =
      trace (numericNeighborhood G) (phaseTwoSample G E A W) b') :
    ∀ a ∈ A,
      (a ∈ numericNeighborhood G b ↔ a ∈ numericNeighborhood G b') := by
  have hlist : (((List.range n).filter fun a => a ∈ A).toFinset) = A := by
    ext a
    by_cases ha : a ∈ A
    · simp [ha, Finset.mem_range.mp (hA ha)]
    · simp [ha]
  intro a ha
  have haList : a ∈ (((List.range n).filter fun v => v ∈ A).toFinset) := by
    rw [hlist]
    exact ha
  exact phase2Scan_separates (numericNeighborhood G) E b b' hb hb'
    ((List.range n).filter fun v => v ∈ A) W
    (by simpa [phaseTwoSample] using htrace) a haList

end

end Lax457868Proofs.ExceptionPhaseSource
