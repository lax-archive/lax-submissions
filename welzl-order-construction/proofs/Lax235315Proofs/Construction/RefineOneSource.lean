import Lax235315Proofs.Construction.MarkingSource
import Lax235315Proofs.Construction.PartitionRefinement
import Lax235315Proofs.Construction.RefineSplitSource
import Mathlib.Tactic

/-! Composition of the three post-scan loops in `refineOne`. -/

namespace Lax235315Proofs.Construction.RefineOneSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.MarkingSource
open Lax235315Proofs.Construction.NeighborScan
open Lax235315Proofs.Construction.PartitionRefinement
open Lax235315Proofs.Construction.RefineSplitMath
open Lax235315Proofs.Construction.RefineSplitSource
open Lax235315Proofs.Construction.WelzlProgram
open Lax11.GraphEncoding
open Lax11Proofs.CC

/-- A numeric binary-refinement certificate for one encoded CSR block is the
graph-theoretic refinement relation on the corresponding active vertex set. -/
theorem refinesBy_of_numeric_block
    {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) {active label label' : ℕ → ℕ}
    (t : Fin n)
    (hrefines :
      ∀ u ∈ activeVertices n active, ∀ v ∈ activeVertices n active,
        (label' u = label' v ↔ label u = label v ∧
          (u ∈ activeTargets (target x) active (offset x t.val)
              (offset x (t.val + 1)) ↔
            v ∈ activeTargets (target x) active (offset x t.val)
              (offset x (t.val + 1))))) :
    RefinesBy G {v : Fin n | active v.val = 1}
      (fun v => label v.val) (fun v => label' v.val) t := by
  have mem_iff (z : Fin n) (hz : active z.val = 1) :
      z.val ∈ activeTargets (target x) active (offset x t.val)
          (offset x (t.val + 1)) ↔ G.Adj t z := by
    rw [mem_activeTargets_block hx t.isLt]
    simp only [hz, true_and]
    constructor
    · rintro ⟨htn, hzn, hadj⟩
      simpa using hadj
    · intro hadj
      exact ⟨t.isLt, z.isLt, hadj⟩
  intro u hu v hv
  have huA : u.val ∈ activeVertices n active :=
    mem_activeVertices.mpr ⟨u.isLt, hu⟩
  have hvA : v.val ∈ activeVertices n active :=
    mem_activeVertices.mpr ⟨v.isLt, hv⟩
  rw [hrefines u.val huA v.val hvA, mem_iff u hu, mem_iff v hv]

/-- The suffix of `refineOne` after its CSR marking scan. -/
def finishRefinement (clsName : String) : Com :=
  seqs [
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "touchedLen")) refineSplitBody,
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "markedLen"))
      (refineRelabelBody clsName),
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "touchedLen")) refineResetBody]

/-- Once the adjacency scan has collected its distinct active targets, the
remaining loops allocate compact classes, relabel exactly those targets, and
restore the marked counters to zero. -/
theorem finishRefinement_run
    {B n targetCap lo hi base token : ℕ}
    {activeName clsName : String}
    {active label size target initialSplit : ℕ → ℕ}
    {σ : Env}
    (hI : MarkInv B n targetCap lo hi base token
      activeName clsName active label size target σ)
    (hj : σ.vars "j" = hi)
    (hoccupied : LabelsOccupyPrefix base label (activeVertices n active))
    (hsplitArray : σ.arrs "split" = arrOf n initialSplit)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hnB : n < B) (honeB : 1 < B)
    (hsizeB : ∀ q < base, size q < B)
    (hactiveCls : activeName ≠ clsName)
    (haSplit : activeName ≠ "split")
    (haSize : activeName ≠ "classSize")
    (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (hcSplit : clsName ≠ "split")
    (hcSize : clsName ≠ "classSize")
    (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount")
    (hcStamp : clsName ≠ "stamp") :
    ∃ σ' current split workSize cleared finalStamp,
      Run B (finishRefinement clsName) σ σ'
        (180 * ((activeTargets target active lo hi).card + 1)) ∧
      σ'.vars "classCount" = current ∧ current ≤ n ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs clsName = arrOf n (refinedLabel
        (activeTargets target active lo hi) label split) ∧
      σ'.arrs "classSize" = arrOf n workSize ∧
      σ'.arrs "markedCount" = arrOf n cleared ∧
      σ'.arrs "stamp" = arrOf n finalStamp ∧
      (∀ v < n, finalStamp v ≤ token) ∧
      (∀ q < n, cleared q = 0) ∧
      ClassSizes n current active
        (refinedLabel (activeTargets target active lo hi) label split) workSize ∧
      LabelsOccupyPrefix current
        (refinedLabel (activeTargets target active lo hi) label split)
        (activeVertices n active) ∧
      ∀ u ∈ activeVertices n active, ∀ v ∈ activeVertices n active,
        (refinedLabel (activeTargets target active lo hi) label split u =
          refinedLabel (activeTargets target active lo hi) label split v ↔
        label u = label v ∧
          (u ∈ activeTargets target active lo hi ↔
            v ∈ activeTargets target active lo hi)) := by
  rcases hI with ⟨stamp, marked, touched, counts, hlo, hjhi, hjend,
    hbase, htoken, hn, hbasen, hhiCap, hactive, hlabel, hsize, htarget,
    hstamp, hcounts, hmarkedStack, htouchedStack, hmarkedEnum,
    htouchedEnum, hstampMem, hstampLe, hstampBound, hcountEq, hsizes⟩
  let M := activeTargets target active lo hi
  let TC := touchedClasses label M
  have hMsub : M ⊆ activeVertices n active := by
    intro v hv
    obtain ⟨hvActive, j, hlj, hjh, rfl⟩ := mem_activeTargets.mp hv
    exact mem_activeVertices.mpr ⟨htargetRange j hlj hjh, hvActive⟩
  have hMcard : M.card ≤ n := by
    exact (Finset.card_le_card hMsub).trans (activeVertices_card_le n active)
  have hTCcard : TC.card ≤ n := by
    exact (Finset.card_image_le.trans hMcard)
  have hTCcardM : TC.card ≤ M.card := by
    simpa [TC, touchedClasses] using
      (Finset.card_image_le : (M.image label).card ≤ M.card)
  have hmarkedArr : σ.arrs "marked" = arrOf n marked := by
    simpa [M, hj] using hmarkedStack.arr
  have hmarkedHeight : σ.vars "markedLen" = M.card := by
    simpa [M, hj] using hmarkedStack.height
  have htouchedArr : σ.arrs "touched" = arrOf n touched := by
    simpa [TC, M, hj] using htouchedStack.arr
  have htouchedHeight : σ.vars "touchedLen" = TC.card := by
    simpa [TC, M, hj] using htouchedStack.height
  have hmarkedEnum' : PrefixEnumerates M.card marked M := by
    simpa [M, hj] using hmarkedEnum
  have htouchedEnum' : PrefixEnumerates TC.card touched TC := by
    simpa [TC, M, hj] using htouchedEnum
  have hcountEq' : ∀ q < n, counts q = classMultiplicity label M q := by
    intro q hq
    simpa [M, hj] using hcountEq q hq
  have hcountEqBase : ∀ q < base, counts q = classMultiplicity label M q := by
    intro q hq
    exact hcountEq' q (hq.trans_le hbasen)
  have hcountB : ∀ q < n, counts q < B := by
    intro q hq
    rw [hcountEq' q hq]
    exact (classMultiplicity_le_card label M q).trans_lt (hMcard.trans_lt hnB)
  have hTCRange : ∀ q ∈ TC, q < base := by
    intro q hq
    obtain ⟨v, hvM, rfl⟩ := mem_touchedClasses.mp hq
    have hvA := hMsub hvM
    exact hsizes.1 v (mem_activeVertices.mp hvA).1
      (mem_activeVertices.mp hvA).2
  have hcapacity : base + (TC.filter fun q => counts q < size q).card ≤ n :=
    hsizes.split_capacity hoccupied hMsub hcountEqBase
  let σ₀ := σ.setVar "i" 0
  have r₀ : Run B (.assign "i" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have hsplitInv₀ : SplitInv n base TC.card touched TC counts size σ₀ := by
    apply splitInv_initial (split := initialSplit)
    · simp [σ₀]
    · exact hTCcard
    · simp [σ₀, hn]
    · simp [σ₀, htouchedHeight]
    · simp [σ₀, hbase]
    · simp [σ₀, htouchedArr]
    · simp [σ₀, hcounts]
    · simp [σ₀, hsize]
    · simp [σ₀, hsplitArray]
    · exact htouchedEnum'
    · exact hTCRange
  obtain ⟨σ₁, reportedCurrent, reportedSplit, reportedWorkSize,
      rsplit, hsplitInv₁, hi₁, hreportedCurrent, hreportedSplit,
      hreportedWorkSize, hreportedValid, hreportedCurrentLe⟩ :=
    refineSplitLoop_run hsplitInv₀ hnB honeB hcapacity hcountB hsizeB
  rcases hsplitInv₁ with ⟨current, split, workSize, hile₁, hheight₁,
    hn₁, htouchedLen₁, hcurrentInv, hentry₁, hcounts₁, hworkInv,
    hsplitInv, henum₁, hrange₁, hprefix₁, hsizes₁, hunchanged₁⟩
  have hprocessedTC : processedClasses TC.card touched = TC :=
    PrefixEnumerates.processedClasses_eq henum₁
  have hprefixFinal : SplitPrefix base current TC counts size split := by
    simpa [hi₁, hcurrentInv, hprocessedTC] using hprefix₁
  have hsplitSizesFinal : SplitSizes TC counts size split workSize := by
    simpa [hi₁, hprocessedTC] using hsizes₁
  have hunchangedFinal : ∀ q < base, q ∉ TC → workSize q = size q := by
    intro q hq hqTC
    apply hunchanged₁ q hq
    simpa [hi₁, hprocessedTC] using hqTC
  have hnew := refinedLabel_classSizes_and_occupancy hMsub hsizes hoccupied
    hcountEqBase hprefixFinal hsplitSizesFinal hunchangedFinal
  have hcurrentLe : current ≤ n := by
    exact (hprefixFinal.current_le (Finset.Subset.rfl)).trans hcapacity
  let σ₂ := σ₁.setVar "i" 0
  have r₂ : Run B (.assign "i" (.lit 0)) σ₁ σ₂ 2 :=
    Run.assign (evalB_lit (by omega))
  have hmarked₁ : σ₁.arrs "marked" = arrOf n marked := by
    rw [rsplit.frame_arr "marked" (by
      simp [refineSplitBody, seqs, inc, Com.warrs])]
    simpa [σ₀] using hmarkedArr
  have hlabel₁ : σ₁.arrs clsName = arrOf n label := by
    rw [rsplit.frame_arr clsName (by
      simp [refineSplitBody, seqs, inc, Com.warrs, hcSplit, hcSize])]
    simpa [σ₀] using hlabel
  have hactive₁ : σ₁.arrs activeName = arrOf n active := by
    rw [rsplit.frame_arr activeName (by
      simp [refineSplitBody, seqs, inc, Com.warrs, haSplit, haSize])]
    simpa [σ₀] using hactive
  have hmarkedLen₁ : σ₁.vars "markedLen" = M.card := by
    rw [rsplit.frame_var "markedLen" (by
      simp [refineSplitBody, seqs, inc, Com.wvars])]
    simpa [σ₀] using hmarkedHeight
  have hlabelN : ∀ v ∈ M, label v < n := by
    intro v hv
    exact (hsizes.1 v (mem_activeVertices.mp (hMsub hv)).1
      (mem_activeVertices.mp (hMsub hv)).2).trans_le hbasen
  have hsplitB : ∀ v ∈ M, split (label v) < B := by
    intro v hv
    have hvA := hMsub hv
    have href : refinedLabel M label split v = split (label v) := by
      simp [refinedLabel, hv]
    rw [← href]
    exact ((hnew.1.1 v (mem_activeVertices.mp hvA).1
      (mem_activeVertices.mp hvA).2).trans_le hcurrentLe).trans hnB
  have hrelabelInv₂ : RelabelInv n M.card marked M clsName label split σ₂ := by
    apply relabelInv_initial
    · simp [σ₂]
    · exact hMcard
    · simp [σ₂, hn₁]
    · simp [σ₂, hmarkedLen₁]
    · simp [σ₂, hmarked₁]
    · simp [σ₂, hsplitInv]
    · simp [σ₂, hlabel₁]
    · exact hmarkedEnum'
  obtain ⟨σ₃, rrelabel, hrelabelInv₃, hi₃, hlabel₃⟩ :=
    refineRelabelLoop_run hrelabelInv₂ hnB honeB
      (fun v hv => (mem_activeVertices.mp (hMsub hv)).1)
      hlabelN hsplitB hcMarked hcSplit
  have hwork₃ : σ₃.arrs "classSize" = arrOf n workSize := by
    rw [rrelabel.frame_arr "classSize" (by
      simp [refineRelabelBody, seqs, inc, Com.warrs, Ne.symm hcSize])]
    simpa [σ₂] using hworkInv
  have hcounts₃ : σ₃.arrs "markedCount" = arrOf n counts := by
    rw [rrelabel.frame_arr "markedCount" (by
      simp [refineRelabelBody, seqs, inc, Com.warrs, Ne.symm hcCount])]
    simpa [σ₂] using hcounts₁
  have htouched₃ : σ₃.arrs "touched" = arrOf n touched := by
    rw [rrelabel.frame_arr "touched" (by
      simp [refineRelabelBody, seqs, inc, Com.warrs, Ne.symm hcTouched])]
    simpa [σ₂] using hentry₁
  have htouchedLen₃ : σ₃.vars "touchedLen" = TC.card := by
    rw [rrelabel.frame_var "touchedLen" (by
      simp [refineRelabelBody, seqs, inc, Com.wvars])]
    simpa [σ₂] using htouchedLen₁
  have hn₃ : σ₃.vars "n" = n := by
    rw [rrelabel.frame_var "n" (by
      simp [refineRelabelBody, seqs, inc, Com.wvars])]
    simpa [σ₂] using hn₁
  let σ₄ := σ₃.setVar "i" 0
  have r₄ : Run B (.assign "i" (.lit 0)) σ₃ σ₄ 2 :=
    Run.assign (evalB_lit (by omega))
  have hresetInv₄ : ResetInv n TC.card touched TC counts σ₄ := by
    apply resetInv_initial
    · simp [σ₄]
    · exact hTCcard
    · simp [σ₄, hn₃]
    · simp [σ₄, htouchedLen₃]
    · simp [σ₄, htouched₃]
    · simp [σ₄, hcounts₃]
    · exact htouchedEnum'
  obtain ⟨σ₅, rreset, hresetInv₅, hi₅, hcleared₅⟩ :=
    refineResetLoop_run hresetInv₄ hnB
      (fun q hq => (hTCRange q hq).trans_le hbasen)
  let cleared := partiallyCleared TC counts
  have hclearedZero : ∀ q < n, cleared q = 0 := by
    intro q hq
    by_cases hqTC : q ∈ TC
    · simp [cleared, partiallyCleared, hqTC]
    · have hzero : classMultiplicity label M q = 0 := by
        exact Nat.eq_zero_of_not_pos
          (fun hp => hqTC (classMultiplicity_pos_iff.mp hp))
      simp [cleared, partiallyCleared, hqTC, hcountEq' q hq, hzero]
  have hactive₅ : σ₅.arrs activeName = arrOf n active := by
    rw [rreset.frame_arr activeName (by
      simp [refineResetBody, seqs, inc, Com.warrs, haCount])]
    rw [r₄.frame_arr activeName (by simp [Com.warrs])]
    rw [rrelabel.frame_arr activeName (by
      simp [refineRelabelBody, seqs, inc, Com.warrs,
        hactiveCls])]
    exact hactive₁
  have hlabel₅ : σ₅.arrs clsName =
      arrOf n (refinedLabel M label split) := by
    rw [rreset.frame_arr clsName (by
      simp [refineResetBody, seqs, inc, Com.warrs, hcCount])]
    simpa [σ₄] using hlabel₃
  have hwork₅ : σ₅.arrs "classSize" = arrOf n workSize := by
    rw [rreset.frame_arr "classSize" (by
      simp [refineResetBody, seqs, inc, Com.warrs])]
    simpa [σ₄] using hwork₃
  have hcurrent₅ : σ₅.vars "classCount" = current := by
    rw [rreset.frame_var "classCount" (by
      simp [refineResetBody, seqs, inc, Com.wvars])]
    rw [r₄.frame_var "classCount" (by decide)]
    rw [rrelabel.frame_var "classCount" (by
      simp [refineRelabelBody, seqs, inc, Com.wvars])]
    simpa [σ₂] using hcurrentInv
  have hstamp₅ : σ₅.arrs "stamp" = arrOf n stamp := by
    rw [rreset.frame_arr "stamp" (by
      simp [refineResetBody, seqs, inc, Com.warrs])]
    rw [r₄.frame_arr "stamp" (by simp [Com.warrs])]
    rw [rrelabel.frame_arr "stamp" (by
      simp [refineRelabelBody, seqs, inc, Com.warrs, Ne.symm hcStamp])]
    rw [r₂.frame_arr "stamp" (by simp [Com.warrs])]
    rw [rsplit.frame_arr "stamp" (by
      simp [refineSplitBody, seqs, inc, Com.warrs])]
    simpa [σ₀] using hstamp
  refine ⟨σ₅, current, split, workSize, cleared, stamp, ?_, hcurrent₅,
    hcurrentLe, hactive₅, hlabel₅, hwork₅, ?_, hstamp₅, hstampLe, hclearedZero,
    hnew.1, hnew.2, ?_⟩
  · have rr := r₀.seq (rsplit.seq (r₂.seq (rrelabel.seq (r₄.seq rreset))))
    have hi₁' := hi₁
    have hi₃' := hi₃
    have hi₅' := hi₅
    dsimp [TC, M] at hTCcardM hi₁' hi₃' hi₅'
    simpa [finishRefinement, seqs, M] using rr.mono (by omega)
  · simpa [cleared] using hcleared₅
  · intro u hu v hv
    exact refinedLabel_eq_iff hMsub hsizes.1 hsizes.2 hcountEqBase
      hprefixFinal.validSplits hu hv

/-- One complete `refineOne` call realizes binary refinement by the distinct
active targets in the selected CSR block. -/
theorem refineOne_run
    {B n targetCap base token t : ℕ}
    {activeName clsName : String}
    {active label size offset target stamp counts marked touched split₀ : ℕ → ℕ}
    {σ : Env}
    (hn : σ.vars "n" = n) (hbase : σ.vars "classCount" = base)
    (htoken : σ.vars "token" = token) (ht : σ.vars "t" = t)
    (hoff : σ.arrs "off" = arrOf (n + 1) offset)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hactive : σ.arrs activeName = arrOf n active)
    (hlabel : σ.arrs clsName = arrOf n label)
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
    (hactiveB : ∀ v < n, active v < B)
    (hsizeB : ∀ q < base, size q < B)
    (hstampNe : ∀ v < n, stamp v ≠ token)
    (hstampLe : ∀ v < n, stamp v ≤ token)
    (hstampB : ∀ v < n, stamp v < B)
    (hcountsZero : ∀ q < n, counts q = 0)
    (hsizes : ClassSizes n base active label size)
    (hoccupied : LabelsOccupyPrefix base label (activeVertices n active))
    (hactiveCls : activeName ≠ clsName)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (haSplit : activeName ≠ "split")
    (haSize : activeName ≠ "classSize")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount")
    (hcSplit : clsName ≠ "split")
    (hcSize : clsName ≠ "classSize") :
    ∃ σ' current split workSize cleared finalStamp,
      Run B (refineOne activeName clsName) σ σ'
        (300 * (offset (t + 1) - offset t + 1)) ∧
      σ'.vars "classCount" = current ∧ current ≤ n ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs clsName = arrOf n (refinedLabel
        (activeTargets target active (offset t) (offset (t + 1)))
        label split) ∧
      σ'.arrs "classSize" = arrOf n workSize ∧
      σ'.arrs "markedCount" = arrOf n cleared ∧
      σ'.arrs "stamp" = arrOf n finalStamp ∧
      (∀ v < n, finalStamp v ≤ token) ∧
      (∀ q < n, cleared q = 0) ∧
      ClassSizes n current active
        (refinedLabel
          (activeTargets target active (offset t) (offset (t + 1)))
          label split) workSize ∧
      LabelsOccupyPrefix current
        (refinedLabel
          (activeTargets target active (offset t) (offset (t + 1)))
          label split) (activeVertices n active) ∧
      ∀ u ∈ activeVertices n active, ∀ v ∈ activeVertices n active,
        (refinedLabel
            (activeTargets target active (offset t) (offset (t + 1)))
            label split u =
          refinedLabel
            (activeTargets target active (offset t) (offset (t + 1)))
            label split v ↔
        label u = label v ∧
          (u ∈ activeTargets target active (offset t) (offset (t + 1)) ↔
            v ∈ activeTargets target active (offset t) (offset (t + 1)))) := by
  let lo := offset t
  let hi := offset (t + 1)
  have htB : t < B := htn.trans hnB
  have htsuccN : t + 1 < n + 1 := by omega
  have htsuccB : t + 1 < B := by omega
  have hloCap : lo ≤ targetCap := hoffRange t (by omega)
  have hhiCap : hi ≤ targetCap := hoffRange (t + 1) htsuccN
  have hloB : lo < B := hloCap.trans_lt htargetCapB
  have hhiB : hi < B := hhiCap.trans_lt htargetCapB
  let σ₀ := σ.setVar "markedLen" 0
  let σ₁ := σ₀.setVar "touchedLen" 0
  let σ₂ := σ₁.setVar "j" lo
  let σ₃ := σ₂.setVar "jend" hi
  have r₀ : Run B (.assign "markedLen" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have r₁ : Run B (.assign "touchedLen" (.lit 0)) σ₀ σ₁ 2 :=
    Run.assign (evalB_lit (by omega))
  have htEval : (Expr.var "t").evalB B σ₁ = some t := by
    rw [evalB_var_iff]
    simp [σ₁, σ₀, ht, htB]
  have hloGet : (σ₁.arrs "off")[t]? = some lo := by
    rw [show σ₁.arrs "off" = arrOf (n + 1) offset by
      simp [σ₁, σ₀, hoff]]
    simpa [lo] using getElem?_arrOf offset (show t < n + 1 by omega)
  have hloEval : (Expr.get "off" (.var "t")).evalB B σ₁ = some lo :=
    evalB_get htEval hloGet hloB
  have r₂ : Run B (.assign "j" (.get "off" (.var "t"))) σ₁ σ₂ 6 :=
    (Run.assign hloEval).mono (by norm_num [Expr.size])
  have hsuccEval : (Expr.add (.var "t") (.lit 1)).evalB B σ₂ =
      some (t + 1) := by
    apply evalB_bin
    · simpa [σ₂] using htEval
    · exact evalB_lit honeB
    · exact htsuccB
  have hhiGet : (σ₂.arrs "off")[t + 1]? = some hi := by
    simp [σ₂, σ₁, σ₀, hoff, hi,
      getElem?_arrOf offset htsuccN]
  have hhiEval : (Expr.get "off" (.add (.var "t") (.lit 1))).evalB B σ₂ =
      some hi := evalB_get hsuccEval hhiGet hhiB
  have r₃ : Run B
      (.assign "jend" (.get "off" (.add (.var "t") (.lit 1))))
      σ₂ σ₃ 8 :=
    (Run.assign hhiEval).mono (by norm_num [Expr.size])
  have hmarkInv₃ : MarkInv B n targetCap lo hi base token
      activeName clsName active label size target σ₃ := by
    apply markInv_initial (stamp := stamp) (marked := marked)
      (touched := touched) (counts := counts)
    · simp [σ₃, σ₂]
    · simp [σ₃]
    · exact hoffMono
    · simp [σ₃, σ₂, σ₁, σ₀, hbase]
    · simp [σ₃, σ₂, σ₁, σ₀, htoken]
    · simp [σ₃, σ₂, σ₁, σ₀, hn]
    · exact hbasen
    · exact hhiCap
    · simp [σ₃, σ₂, σ₁, σ₀, hactive]
    · simp [σ₃, σ₂, σ₁, σ₀, hlabel]
    · simp [σ₃, σ₂, σ₁, σ₀, hsize]
    · simp [σ₃, σ₂, σ₁, σ₀, htarget]
    · simp [σ₃, σ₂, σ₁, σ₀, hstamp]
    · simp [σ₃, σ₂, σ₁, σ₀, hcounts]
    · simp [σ₃, σ₂, σ₁, σ₀, hmarked]
    · simp [σ₃, σ₂, σ₁, σ₀, htouched]
    · simp [σ₃, σ₂, σ₁, σ₀]
    · simp [σ₃, σ₂, σ₁, σ₀]
    · exact hstampNe
    · exact hstampLe
    · exact hstampB
    · exact hcountsZero
    · exact hsizes
  obtain ⟨σ₄, rmark, hmarkInv₄, hj₄⟩ :=
    refineMarkLoop_run hmarkInv₃
      (by simpa [lo, hi] using htargetRange) hactiveB hnB htargetCapB
      htokenB honeB haStamp haMarked haTouched haCount
      hcStamp hcMarked hcTouched hcCount
  have hsplit₄ : σ₄.arrs "split" = arrOf n split₀ := by
    rw [rmark.frame_arr "split" (by
      simp [refineMarkBody, seqs, inc, Com.warrs])]
    simp [σ₃, σ₂, σ₁, σ₀, hsplit]
  obtain ⟨σ₅, current, split, workSize, cleared, finalStamp, rfinish,
      hcurrent, hcurrentLe, hactive₅, hlabel₅, hwork₅, hcleared₅,
      hstamp₅, hstampLe₅, hclearedZero, hnewSizes, hnewOccupied, hrefines⟩ :=
    finishRefinement_run hmarkInv₄ hj₄ hoccupied hsplit₄
      (by simpa [lo, hi] using htargetRange) hnB honeB hsizeB hactiveCls
      haSplit haSize haMarked haTouched haCount
      hcSplit hcSize hcMarked hcTouched hcCount hcStamp
  have hmarkedCard :
      (activeTargets target active lo hi).card ≤ hi - lo :=
    card_activeTargets_le_interval
  refine ⟨σ₅, current, split, workSize, cleared, finalStamp, ?_, hcurrent,
    hcurrentLe, hactive₅, ?_, hwork₅, hcleared₅, hstamp₅, hstampLe₅, hclearedZero,
    ?_, ?_, ?_⟩
  · have rr := r₀.seq (r₁.seq (r₂.seq (r₃.seq (rmark.seq rfinish))))
    simpa [refineOne, finishRefinement, refineSplitBody, refineRelabelBody,
      refineResetBody, seqs, lo, hi] using
      rr.mono (by omega)
  · simpa [lo, hi] using hlabel₅
  · simpa [lo, hi] using hnewSizes
  · simpa [lo, hi] using hnewOccupied
  · simpa [lo, hi] using hrefines

end Lax235315Proofs.Construction.RefineOneSource
