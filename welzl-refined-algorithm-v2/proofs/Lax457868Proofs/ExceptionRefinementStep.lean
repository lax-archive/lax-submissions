import Lax457868Proofs.ExceptionRefinementBridge

/-! One phase-two candidate step: refine the exception partition by the
candidate's CSR block, then mark that candidate exactly when the number of
exception classes grows. -/

namespace Lax457868Proofs.ExceptionRefinementStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerRefinementBudget
open Lax457868Proofs.ExceptionRefinementBridge
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax457868Proofs.ReusedOriginal.Construction.RefineSplitMath
open Lax457868Proofs.ReusedOriginal.Construction.RefineOneSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- Zero-one array for a finite vertex set. -/
def setFlag (S : Finset ℕ) (v : ℕ) : ℕ := if v ∈ S then 1 else 0

private lemma activeVertices_setFlag {n : ℕ} {E : Finset ℕ}
    (hE : E ⊆ Finset.range n) : activeVertices n (setFlag E) = E := by
  ext v
  simp only [mem_activeVertices, setFlag]
  constructor
  · rintro ⟨_, hv⟩
    by_cases h : v ∈ E <;> simp [h] at hv ⊢
  · intro hv
    exact ⟨Finset.mem_range.mp (hE hv), by simp [hv]⟩

private lemma setFlag_insert (W : Finset ℕ) (t : ℕ) :
    upd (setFlag W) t 1 = setFlag (insert t W) := by
  funext v
  by_cases hv : v = t
  · subst v
    simp [setFlag, upd]
  · simp [setFlag, upd, hv]

/-- The actual source code for one candidate.  The outer scan supplies `t`
and a fresh `token`; this step saves the old class count before refinement. -/
def exceptionRefinementStep : Com :=
  seqs [
    .assign "phase2OldCount" (.var "classCount"),
    refineOne "exceptionFlags" "classB",
    .ite (.lt (.var "phase2OldCount") (.var "classCount"))
      (.store "sampleFlags" (.var "t") (.lit 1)) .skip]

private lemma refined_labels_classify_step
    {base current t : ℕ} {N : ℕ → Finset ℕ}
    {E W : Finset ℕ} {label newLabel : ℕ → ℕ}
    (hrange : ∀ b ∈ E, label b < base)
    (hoccupied : LabelsOccupyPrefix base label E)
    (hclassify : ∀ b ∈ E, ∀ b' ∈ E,
      (label b = label b' ↔ trace N W b = trace N W b'))
    (hnewRange : ∀ b ∈ E, newLabel b < current)
    (hnewOccupied : LabelsOccupyPrefix current newLabel E)
    (hrefine : ∀ b ∈ E, ∀ b' ∈ E,
      (newLabel b = newLabel b' ↔
        label b = label b' ∧ (t ∈ N b ↔ t ∈ N b'))) :
    ∀ b ∈ E, ∀ b' ∈ E,
      (newLabel b = newLabel b' ↔
        trace N (phase2Step N E W t) b =
          trace N (phase2Step N E W t) b') := by
  have hstep := phase2Step_eq_if_refinedClassCount_gt N E W t
    label newLabel base current hrange hoccupied hclassify
    hnewRange hnewOccupied hrefine
  have hgrowthIff := refinedClassCount_gt_iff_splits N E W t
    label newLabel base current hrange hoccupied hclassify
    hnewRange hnewOccupied hrefine
  intro b hb b' hb'
  by_cases hlt : base < current
  · rw [hstep, if_pos hlt]
    rw [trace_insert_eq_iff]
    rw [hrefine b hb b' hb', hclassify b hb b' hb']
  · rw [hstep, if_neg hlt]
    have hnosplit : ¬ splitsExceptionPair N E W t := by
      intro hs
      exact hlt (hgrowthIff.mpr hs)
    have hmem : trace N W b = trace N W b' →
        (t ∈ N b ↔ t ∈ N b') := by
      intro htr
      by_contra hdiff
      have hcases : (t ∈ N b ∧ t ∉ N b') ∨
          (t ∉ N b ∧ t ∈ N b') := by tauto
      exact hnosplit ⟨b, b', hb, hb', htr, hcases⟩
    rw [hrefine b hb b' hb']
    constructor
    · intro h
      exact (hclassify b hb b' hb').mp h.1
    · intro h
      exact ⟨(hclassify b hb b' hb').mpr h, hmem h⟩

/-- A complete source step for one candidate.  Its CSR block is assumed to
encode the candidate's neighborhood on the active exceptions.  The returned
labels classify the updated sample even when refinement changes labels but
does not increase the class count. -/
lemma exceptionRefinementStep_run
    {B n targetCap base token t : ℕ} {σ : Env}
    {N : ℕ → Finset ℕ} {E W : Finset ℕ}
    {label size offset target stamp counts marked touched split₀ : ℕ → ℕ}
    (hE : E ⊆ Finset.range n)
    (hW : W ⊆ Finset.range n)
    (hclassify : ∀ b ∈ E, ∀ b' ∈ E,
      (label b = label b' ↔ trace N W b = trace N W b'))
    (hCSR : ∀ b ∈ E,
      (b ∈ activeTargets target (setFlag E) (offset t) (offset (t + 1)) ↔
        t ∈ N b))
    (hn : σ.vars "n" = n) (hbase : σ.vars "classCount" = base)
    (htoken : σ.vars "token" = token) (ht : σ.vars "t" = t)
    (hoff : σ.arrs "off" = arrOf (n + 1) offset)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hactive : σ.arrs "exceptionFlags" = arrOf n (setFlag E))
    (hlabel : σ.arrs "classB" = arrOf n label)
    (hsample : σ.arrs "sampleFlags" = arrOf n (setFlag W))
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hcounts : σ.arrs "markedCount" = arrOf n counts)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hsplit : σ.arrs "split" = arrOf n split₀)
    (htn : t < n) (hbasen : base ≤ n)
    (hoffMono : offset t ≤ offset (t + 1))
    (hoffRange : ∀ i < n + 1, offset i ≤ targetCap)
    (htargetRange : ∀ j, offset t ≤ j → j < offset (t + 1) →
      target j < n)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (htokenB : token < B) (honeB : 1 < B)
    (hsizeB : ∀ q < base, size q < B)
    (hstampNe : ∀ v < n, stamp v ≠ token)
    (hstampLe : ∀ v < n, stamp v ≤ token)
    (hstampB : ∀ v < n, stamp v < B)
    (hcountsZero : ∀ q < n, counts q = 0)
    (hsizes : ClassSizes n base (setFlag E) label size)
    (hoccupied : LabelsOccupyPrefix base label E) :
    ∃ σ' current split workSize cleared finalStamp,
      Run B exceptionRefinementStep σ σ'
        (300 * (offset (t + 1) - offset t + 1) + 9) ∧
      σ'.vars "phase2OldCount" = base ∧
      σ'.vars "classCount" = current ∧ current ≤ n ∧ base ≤ current ∧
      (base < current ↔ splitsExceptionPair N E W t) ∧
      σ'.arrs "exceptionFlags" = arrOf n (setFlag E) ∧
      σ'.arrs "classB" = arrOf n
        (refinedLabel
          (activeTargets target (setFlag E) (offset t) (offset (t + 1)))
          label split) ∧
      σ'.arrs "sampleFlags" = arrOf n (setFlag (phase2Step N E W t)) ∧
      σ'.arrs "classSize" = arrOf n workSize ∧
      σ'.arrs "markedCount" = arrOf n cleared ∧
      σ'.arrs "stamp" = arrOf n finalStamp ∧
      (∀ v < n, finalStamp v ≤ token) ∧
      (∀ q < n, cleared q = 0) ∧
      ClassSizes n current (setFlag E)
        (refinedLabel
          (activeTargets target (setFlag E) (offset t) (offset (t + 1)))
          label split) workSize ∧
      LabelsOccupyPrefix current
        (refinedLabel
          (activeTargets target (setFlag E) (offset t) (offset (t + 1)))
          label split) E ∧
      (∀ b ∈ E, ∀ b' ∈ E,
        (refinedLabel
            (activeTargets target (setFlag E) (offset t) (offset (t + 1)))
            label split b =
          refinedLabel
            (activeTargets target (setFlag E) (offset t) (offset (t + 1)))
            label split b' ↔
          trace N (phase2Step N E W t) b =
            trace N (phase2Step N E W t) b')) ∧
      (phase2Step N E W t ⊆ Finset.range n) ∧
      σ'.vars "n" = n ∧ σ'.vars "token" = token ∧
      σ'.vars "t" = t ∧
      σ'.arrs "off" = arrOf (n + 1) offset ∧
      σ'.arrs "tgt" = arrOf targetCap target ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (∀ a, a ≠ "sampleFlags" →
        a ∉ (refineOne "exceptionFlags" "classB").warrs →
        σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ≠ "phase2OldCount" →
        x ∉ (refineOne "exceptionFlags" "classB").wvars →
        σ'.vars x = σ.vars x) := by
  have hactiveEq : activeVertices n (setFlag E) = E :=
    activeVertices_setFlag hE
  have hoccupied' : LabelsOccupyPrefix base label
      (activeVertices n (setFlag E)) := by simpa [hactiveEq] using hoccupied
  have hactiveB : ∀ v < n, setFlag E v < B := by
    intro v hv
    by_cases h : v ∈ E <;> simp [setFlag, h] <;> omega
  let σ₀ := σ.setVar "phase2OldCount" base
  have hbaseB : base < B := hbasen.trans_lt hnB
  have hsave : Run B (.assign "phase2OldCount" (.var "classCount"))
      σ σ₀ 2 := by
    simpa [σ₀, hbase] using
      (Run.assign (evalB_var (by rw [hbase]; exact hbaseB :
        σ.vars "classCount" < B)))
  obtain ⟨σ₁, current, split, workSize, cleared, finalStamp,
    hrefRun, hcurrent₁, hcurrentLe, hactive₁, hlabel₁,
    hsize₁, hcounts₁, hstamp₁, hstampLe₁, hcountsZero₁,
    hnewSizes, hnewOccupied₁, hrefine₁⟩ :=
    refineOne_run (σ := σ₀) (activeName := "exceptionFlags")
      (clsName := "classB")
      (by simpa [σ₀] using hn) (by simp [σ₀, hbase])
      (by simpa [σ₀] using htoken) (by simpa [σ₀] using ht)
      (by simpa [σ₀] using hoff) (by simpa [σ₀] using htarget)
      (by simpa [σ₀] using hactive) (by simpa [σ₀] using hlabel)
      (by simpa [σ₀] using hsize) (by simpa [σ₀] using hstamp)
      (by simpa [σ₀] using hcounts) (by simpa [σ₀] using hmarked)
      (by simpa [σ₀] using htouched) (by simpa [σ₀] using hsplit)
      htn hbasen hoffMono hoffRange htargetRange hnB htargetCapB
      htokenB honeB hactiveB hsizeB hstampNe hstampLe hstampB
      hcountsZero hsizes hoccupied'
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide)
  let M := activeTargets target (setFlag E) (offset t) (offset (t + 1))
  let newLabel := refinedLabel M label split
  have hnewOccupied : LabelsOccupyPrefix current newLabel E := by
    simpa [newLabel, M, hactiveEq] using hnewOccupied₁
  have hnewRange : ∀ b ∈ E, newLabel b < current := by
    intro b hb
    exact hnewSizes.1 b (Finset.mem_range.mp (hE hb))
      (by simp [setFlag, hb])
  have hrange : ∀ b ∈ E, label b < base := by
    intro b hb
    exact hsizes.1 b (Finset.mem_range.mp (hE hb))
      (by simp [setFlag, hb])
  have hpair : ∀ b ∈ E, ∀ b' ∈ E,
      (newLabel b = newLabel b' ↔
        label b = label b' ∧ (t ∈ N b ↔ t ∈ N b')) := by
    intro b hb b' hb'
    have hbA : b ∈ activeVertices n (setFlag E) := by simpa [hactiveEq] using hb
    have hb'A : b' ∈ activeVertices n (setFlag E) := by simpa [hactiveEq] using hb'
    simpa [newLabel, M, (hCSR b hb), (hCSR b' hb')] using
      hrefine₁ b hbA b' hb'A
  have hgrowthIff := refinedClassCount_gt_iff_splits N E W t
    label newLabel base current hrange hoccupied hclassify
    hnewRange hnewOccupied hpair
  have hstep := phase2Step_eq_if_refinedClassCount_gt N E W t
    label newLabel base current hrange hoccupied hclassify
    hnewRange hnewOccupied hpair
  have hclassifyStep := refined_labels_classify_step hrange hoccupied
    hclassify hnewRange hnewOccupied hpair
  have hbaseLe : base ≤ current := by
    have hq := classCount_eq_traceClasses_card N W label base
      hrange hoccupied hclassify
    have hq' := classCount_eq_traceClasses_card N (insert t W)
      newLabel current hnewRange hnewOccupied (by
        intro b hb b' hb'
        rw [hpair b hb b' hb', hclassify b hb b' hb']
        exact (trace_insert_eq_iff N W t b b').symm)
    rw [hq, hq']
    exact traceClasses_card_mono E (by
      intro a ha
      exact Finset.mem_insert_of_mem ha)
  have hcurrentB : current < B := hcurrentLe.trans_lt hnB
  have hOld₁ : σ₁.vars "phase2OldCount" = base := by
    rw [hrefRun.frame_var "phase2OldCount" (by decide)]
    simp [σ₀]
  have hsample₁ : σ₁.arrs "sampleFlags" = arrOf n (setFlag W) := by
    rw [hrefRun.frame_arr "sampleFlags" (by decide)]
    simpa [σ₀] using hsample
  have hn₁ : σ₁.vars "n" = n := by
    rw [hrefRun.frame_var "n" (by decide)]
    simpa [σ₀] using hn
  have htoken₁ : σ₁.vars "token" = token := by
    rw [hrefRun.frame_var "token" (by decide)]
    simpa [σ₀] using htoken
  have ht₁ : σ₁.vars "t" = t := by
    rw [hrefRun.frame_var "t" (by decide)]
    simpa [σ₀] using ht
  have hoff₁ : σ₁.arrs "off" = arrOf (n + 1) offset := by
    rw [hrefRun.frame_arr "off" (by decide)]
    simpa [σ₀] using hoff
  have htarget₁ : σ₁.arrs "tgt" = arrOf targetCap target := by
    rw [hrefRun.frame_arr "tgt" (by decide)]
    simpa [σ₀] using htarget
  have hinp₁ : σ₁.inp = σ.inp := by
    exact (hrefRun.frame_inp (by decide)).trans (by simp [σ₀])
  have hout₁ : σ₁.out = σ.out := by
    exact (hrefRun.out_eq (by decide)).trans (by simp [σ₀])
  have harrayFrame₁ (a : String)
      (ha : a ∉ (refineOne "exceptionFlags" "classB").warrs) :
      σ₁.arrs a = σ.arrs a := by
    exact (hrefRun.frame_arr a ha).trans (by simp [σ₀])
  have hvarFrame₁ (x : String) (hx : x ≠ "phase2OldCount")
      (hsource : x ∉ (refineOne "exceptionFlags" "classB").wvars) :
      σ₁.vars x = σ.vars x := by
    exact (hrefRun.frame_var x hsource).trans (by simp [σ₀, hx])
  have hstepRange : phase2Step N E W t ⊆ Finset.range n := by
    rw [hstep]
    by_cases hg : base < current
    · simp only [if_pos hg]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxW
      · exact Finset.mem_range.mpr htn
      · exact hW hxW
    · simpa [hg] using hW
  by_cases hgrowth : base < current
  · have htest : (Cond.lt (.var "phase2OldCount") (.var "classCount")).evalB B σ₁ =
        some true := by
      simpa [hOld₁, hcurrent₁, hgrowth] using
        evalB_condLt (evalB_var (by rw [hOld₁]; exact hbaseB :
          σ₁.vars "phase2OldCount" < B))
          (evalB_var (by rw [hcurrent₁]; exact hcurrentB :
            σ₁.vars "classCount" < B))
    let σ₂ := σ₁.setArr "sampleFlags" t 1
    have hstore : Run B (.store "sampleFlags" (.var "t") (.lit 1))
        σ₁ σ₂ 3 := by
      simpa [σ₂, ht₁] using (Run.store
        (evalB_var (by rw [ht₁]; exact htn.trans hnB : σ₁.vars "t" < B))
        (evalB_lit honeB)
        (by rw [hsample₁, length_arrOf, ht₁]; exact htn))
    have hbranch : Run B
        (.ite (.lt (.var "phase2OldCount") (.var "classCount"))
          (.store "sampleFlags" (.var "t") (.lit 1)) .skip)
        σ₁ σ₂ 7 := by
      have h := Run.ite_true (d := .skip) htest hstore
      simpa using h
    have hrun : Run B exceptionRefinementStep σ σ₂
        (300 * (offset (t + 1) - offset t + 1) + 9) := by
      have h := Run.seq hsave (Run.seq hrefRun hbranch)
      exact h.mono (by omega)
    have hsample₂ : σ₂.arrs "sampleFlags" =
        arrOf n (setFlag (phase2Step N E W t)) := by
      have hsample' : σ₂.arrs "sampleFlags" =
          arrOf n (upd (setFlag W) t 1) := by
        simp [σ₂, hsample₁, set_arrOf_eq_upd]
      rw [hstep, if_pos hgrowth, ← setFlag_insert]
      exact hsample'
    refine ⟨σ₂, current, split, workSize, cleared, finalStamp,
      hrun, ?_, ?_, hcurrentLe, hbaseLe, hgrowthIff, ?_, ?_, hsample₂,
      ?_, ?_, ?_, hstampLe₁, hcountsZero₁, hnewSizes,
      ?_, ?_, hstepRange, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [σ₂] using hOld₁
    · simpa [σ₂] using hcurrent₁
    · simpa [σ₂] using hactive₁
    · simpa [σ₂] using hlabel₁
    · simpa [σ₂] using hsize₁
    · simpa [σ₂] using hcounts₁
    · simpa [σ₂] using hstamp₁
    · simpa [hactiveEq] using hnewOccupied₁
    · exact hclassifyStep
    · simpa [σ₂] using hn₁
    · simpa [σ₂] using htoken₁
    · simpa [σ₂] using ht₁
    · simpa [σ₂] using hoff₁
    · simpa [σ₂] using htarget₁
    · simpa [σ₂] using hinp₁
    · simpa [σ₂] using hout₁
    · intro a ha hsource
      exact (hbranch.frame_arr a (by simp [Com.warrs, ha])).trans
        (harrayFrame₁ a hsource)
    · intro x hx hsource
      exact (hbranch.frame_var x (by simp [Com.wvars])).trans
        (hvarFrame₁ x hx hsource)
  · have htest : (Cond.lt (.var "phase2OldCount") (.var "classCount")).evalB B σ₁ =
        some false := by
      simpa [hOld₁, hcurrent₁, Nat.not_lt.mpr (Nat.le_of_not_gt hgrowth)] using
        evalB_condLt (evalB_var (by rw [hOld₁]; exact hbaseB :
          σ₁.vars "phase2OldCount" < B))
          (evalB_var (by rw [hcurrent₁]; exact hcurrentB :
            σ₁.vars "classCount" < B))
    have hbranch : Run B
        (.ite (.lt (.var "phase2OldCount") (.var "classCount"))
          (.store "sampleFlags" (.var "t") (.lit 1)) .skip)
        σ₁ σ₁ 5 := by
      simpa using (Run.ite_false htest Run.skip)
    have hrun : Run B exceptionRefinementStep σ σ₁
        (300 * (offset (t + 1) - offset t + 1) + 9) := by
      have h := Run.seq hsave (Run.seq hrefRun hbranch)
      exact h.mono (by omega)
    have hsampleStep : σ₁.arrs "sampleFlags" =
        arrOf n (setFlag (phase2Step N E W t)) := by
      simpa [hstep, hgrowth] using hsample₁
    refine ⟨σ₁, current, split, workSize, cleared, finalStamp,
      hrun, hOld₁, hcurrent₁, hcurrentLe, hbaseLe, hgrowthIff,
      hactive₁, hlabel₁, hsampleStep, hsize₁, hcounts₁, hstamp₁,
      hstampLe₁, hcountsZero₁, hnewSizes, ?_, hclassifyStep,
      hstepRange, hn₁, htoken₁, ht₁, hoff₁, htarget₁,
      hinp₁, hout₁, ?_, ?_⟩
    · simpa [hactiveEq] using hnewOccupied₁
    · intro a ha hsource
      exact harrayFrame₁ a hsource
    · intro x hx hsource
      exact hvarFrame₁ x hx hsource

end Lax457868Proofs.ExceptionRefinementStep
