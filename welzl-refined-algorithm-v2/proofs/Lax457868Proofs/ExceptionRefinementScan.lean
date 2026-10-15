import Lax457868Proofs.ExceptionRefinementStep
import Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight
import Lax457868Proofs.ReusedOriginal.Construction.RadixEight

/-! Scan the actual candidate vertices in numeric order, refining the
exception trace partition and marking only class-splitting candidates. -/

namespace Lax457868Proofs.ExceptionRefinementScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax457868Proofs.ReusedOriginal.Construction.RefineSplitMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight

/-- Sample after considering the first `i` candidate indices. -/
def scanSample (N : ℕ → Finset ℕ) (E A W : Finset ℕ) : ℕ → Finset ℕ
  | 0 => W
  | i + 1 =>
      if i ∈ A then phase2Step N E (scanSample N E A W i) i
      else scanSample N E A W i

private lemma phase2Scan_append (N : ℕ → Finset ℕ) (E : Finset ℕ)
    (xs ys : List ℕ) (W : Finset ℕ) :
    phase2Scan N E (xs ++ ys) W =
      phase2Scan N E ys (phase2Scan N E xs W) := by
  induction xs generalizing W with
  | nil => rfl
  | cons a xs ih => simpa [phase2Scan] using ih (phase2Step N E W a)

private lemma scanSample_eq_phase2Scan (N : ℕ → Finset ℕ)
    (E A W : Finset ℕ) (i : ℕ) :
    scanSample N E A W i =
      phase2Scan N E ((List.range i).filter fun a => a ∈ A) W := by
  induction i with
  | zero => simp [scanSample, phase2Scan]
  | succ i ih =>
      rw [scanSample, List.range_succ, List.filter_append,
        phase2Scan_append, ← ih]
      by_cases hi : i ∈ A <;> simp [hi, phase2Scan]

private lemma scanSample_range {n : ℕ} (N : ℕ → Finset ℕ)
    (E A W : Finset ℕ) (hA : A ⊆ Finset.range n)
    (hW : W ⊆ Finset.range n) :
    ∀ i, scanSample N E A W i ⊆ Finset.range n := by
  intro i
  induction i with
  | zero => exact hW
  | succ i ih =>
      simp only [scanSample]
      by_cases hi : i ∈ A
      · simp only [if_pos hi]
        have hii := Finset.mem_range.mp (hA hi)
        have hstep : phase2Step N E (scanSample N E A W i) i ⊆
            insert i (scanSample N E A W i) := by
          simp [phase2Step]
          split_ifs <;> simp
        intro v hv
        rcases Finset.mem_insert.mp (hstep hv) with rfl | hv'
        · exact Finset.mem_range.mpr hii
        · exact ih hv'
      · simpa [hi] using ih

/-- Source body for one candidate index. -/
def exceptionScanBody : Com :=
  seqs [
    .ite (.eq (.get "activeA" (.var "phase2Cursor")) (.lit 1))
      (seqs [
        .assign "token" (.add (.var "phase2Cursor") (.lit 1)),
        .assign "t" (.var "phase2Cursor"),
        exceptionRefinementStep])
      .skip,
    inc "phase2Cursor"]

/-- Clear stamps once, then visit every candidate in order. -/
def exceptionRefinementScan : Com :=
  seqs [
    clearArray "stamp" "n",
    .assign "phase2Cursor" (.lit 0),
    .while (.lt (.var "phase2Cursor") (.var "n")) exceptionScanBody]

/-- All data needed to continue the scan from cursor `i`.  The class labels
represent the traces on the sample accumulated through that cursor. -/
def ScanInv (n targetCap : ℕ) (N : ℕ → Finset ℕ)
    (E A W : Finset ℕ) (offset target : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ i current label size stamp counts marked touched split,
    i ≤ n ∧ τ.vars "phase2Cursor" = i ∧ τ.vars "n" = n ∧
    τ.vars "classCount" = current ∧ current ≤ n ∧
    τ.arrs "off" = arrOf (n + 1) offset ∧
    τ.arrs "tgt" = arrOf targetCap target ∧
    τ.arrs "activeA" = arrOf n (setFlag A) ∧
    τ.arrs "exceptionFlags" = arrOf n (setFlag E) ∧
    τ.arrs "sampleFlags" = arrOf n (setFlag (scanSample N E A W i)) ∧
    τ.arrs "classB" = arrOf n label ∧
    τ.arrs "classSize" = arrOf n size ∧
    τ.arrs "stamp" = arrOf n stamp ∧
    τ.arrs "markedCount" = arrOf n counts ∧
    τ.arrs "marked" = arrOf n marked ∧
    τ.arrs "touched" = arrOf n touched ∧
    τ.arrs "split" = arrOf n split ∧
    (∀ v < n, stamp v ≤ i) ∧
    (∀ q < n, counts q = 0) ∧
    ClassSizes n current (setFlag E) label size ∧
    LabelsOccupyPrefix current label E ∧
    ∀ b ∈ E, ∀ b' ∈ E,
      (label b = label b' ↔
        trace N (scanSample N E A W i) b =
          trace N (scanSample N E A W i) b')

private lemma scanBody_run
    {B n targetCap : ℕ} {N : ℕ → Finset ℕ}
    {E A W : Finset ℕ} {offset target : ℕ → ℕ} {τ : Env}
    (hE : E ⊆ Finset.range n) (hA : A ⊆ Finset.range n)
    (hW : W ⊆ Finset.range n)
    (hCSR : ∀ i ∈ A, ∀ b ∈ E,
      (b ∈ activeTargets target (setFlag E) (offset i) (offset (i + 1)) ↔
        i ∈ N b))
    (hoffMono : ∀ i < n, offset i ≤ offset (i + 1))
    (hoffRange : ∀ i < n + 1, offset i ≤ targetCap)
    (htargetRange : ∀ i < n, ∀ j, offset i ≤ j → j < offset (i + 1) →
      target j < n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hI : ScanInv n targetCap N E A W offset target τ)
    (hcursorLt : τ.vars "phase2Cursor" < n) :
    ∃ τ', Run B exceptionScanBody τ τ'
        (300 * (offset (τ.vars "phase2Cursor" + 1) -
          offset (τ.vars "phase2Cursor") + 1) + 24) ∧
      ScanInv n targetCap N E A W offset target τ' ∧
      τ'.vars "phase2Cursor" = τ.vars "phase2Cursor" + 1 := by
  rcases hI with ⟨i, current, label, size, stamp, counts, marked, touched,
    split, hiLe, hcursor, hn, hcurrent, hcurrentLe, hoff, htarget,
    hactiveA, hactiveE, hsample, hlabel, hsize, hstamp, hcounts,
    hmarked, htouched, hsplit, hstampLe, hcountsZero,
    hsizes, hoccupied, hclassify⟩
  have hiN : i < n := by simpa [hcursor] using hcursorLt
  have hiB : i < B := hiN.trans hnB
  have hnextB : i + 1 < B := by omega
  have hget : (Expr.get "activeA" (.var "phase2Cursor")).evalB B τ =
      some (setFlag A i) := by
    apply evalB_get (evalB_var (by rw [hcursor]; exact hiB))
    · rw [hactiveA, hcursor, getElem?_arrOf _ hiN]
    · by_cases h : i ∈ A <;> simp [setFlag, h] <;> omega
  by_cases hiA : i ∈ A
  · have htest : (Cond.eq (.get "activeA" (.var "phase2Cursor"))
        (.lit 1)).evalB B τ = some true := by
      simpa [setFlag, hiA] using evalB_condEq hget (evalB_lit honeB)
    let τ₁ := τ.setVar "token" (i + 1)
    let τ₂ := τ₁.setVar "t" i
    have rtoken : Run B
        (.assign "token" (.add (.var "phase2Cursor") (.lit 1)))
        τ τ₁ 4 := by
      have hvar : (Expr.var "phase2Cursor").evalB B τ = some i := by
        rw [evalB_var_iff]
        exact ⟨hcursor.symm, by rw [hcursor]; exact hiB⟩
      have heval : (Expr.add (.var "phase2Cursor") (.lit 1)).evalB B τ =
          some (i + 1) := evalB_bin hvar (evalB_lit honeB) hnextB
      simpa [τ₁] using (Run.assign heval)
    have rt : Run B (.assign "t" (.var "phase2Cursor")) τ₁ τ₂ 2 := by
      have hvar : (Expr.var "phase2Cursor").evalB B τ₁ = some i := by
        rw [evalB_var_iff]
        exact ⟨by simp [τ₁, hcursor], by simp [τ₁, hcursor]; exact hiB⟩
      simpa [τ₂] using (Run.assign hvar)
    have hsizeB : ∀ q < current, size q < B := by
      intro q hq
      rw [hsizes.2 q hq]
      calc
        classMultiplicity label (activeVertices n (setFlag E)) q ≤
            (activeVertices n (setFlag E)).card :=
          classMultiplicity_le_card _ _ _
        _ ≤ n := activeVertices_card_le n (setFlag E)
        _ < B := hnB
    have hstampNe : ∀ v < n, stamp v ≠ i + 1 := by
      intro v hv heq
      have h := hstampLe v hv
      omega
    have hstampBound : ∀ v < n, stamp v < B := by
      intro v hv
      exact lt_of_le_of_lt (hstampLe v hv) hiB
    have hsampleRange := scanSample_range N E A W hA hW i
    obtain ⟨τ₃, nextCount, nextSplit, nextSize, nextCounts, nextStamp,
      rstep, _hold, hnextCount, hnextLe, _hbaseLe, _hgrowth,
      hactiveE₃, hlabel₃, hsample₃, hsize₃, hcounts₃, hstamp₃,
      hstampLe₃, hcountsZero₃, hnewSizes, hnewOccupied,
      hclassify₃, _hstepRange, hn₃, _htoken₃, _ht₃,
      hoff₃, htarget₃, _hinp₃, _hout₃, harrayFrame₃,
      hvarFrame₃⟩ :=
      exceptionRefinementStep_run (σ := τ₂) hE hsampleRange hclassify
        (hCSR i hiA)
        (by simpa [τ₂, τ₁] using hn)
        (by simpa [τ₂, τ₁] using hcurrent)
        (by simp [τ₂, τ₁]) (by simp [τ₂, τ₁])
        (by simpa [τ₂, τ₁] using hoff)
        (by simpa [τ₂, τ₁] using htarget)
        (by simpa [τ₂, τ₁] using hactiveE)
        (by simpa [τ₂, τ₁] using hlabel)
        (by simpa [τ₂, τ₁] using hsample)
        (by simpa [τ₂, τ₁] using hsize)
        (by simpa [τ₂, τ₁] using hstamp)
        (by simpa [τ₂, τ₁] using hcounts)
        (by simpa [τ₂, τ₁] using hmarked)
        (by simpa [τ₂, τ₁] using htouched)
        (by simpa [τ₂, τ₁] using hsplit)
        hiN hcurrentLe (hoffMono i hiN) hoffRange
        (htargetRange i hiN) hnB htargetCapB hnextB honeB
        hsizeB hstampNe (fun v hv => (hstampLe v hv).trans (by omega))
        hstampBound hcountsZero hsizes hoccupied
    have hactiveA₃ : τ₃.arrs "activeA" = arrOf n (setFlag A) := by
      rw [harrayFrame₃ "activeA" (by decide) (by decide)]
      simpa [τ₂, τ₁] using hactiveA
    have hcursor₃ : τ₃.vars "phase2Cursor" = i := by
      rw [hvarFrame₃ "phase2Cursor" (by decide) (by decide)]
      simp [τ₂, τ₁, hcursor]
    have hmarkedLen : (τ₃.arrs "marked").length = n := by
      rw [run_array_length_eq rstep "marked"]
      simp [τ₂, τ₁, hmarked, length_arrOf]
    obtain ⟨marked', hmarked₃⟩ := exists_arrOf_of_length hmarkedLen
    have htouchedLen : (τ₃.arrs "touched").length = n := by
      rw [run_array_length_eq rstep "touched"]
      simp [τ₂, τ₁, htouched, length_arrOf]
    obtain ⟨touched', htouched₃⟩ := exists_arrOf_of_length htouchedLen
    have hsplitLen : (τ₃.arrs "split").length = n := by
      rw [run_array_length_eq rstep "split"]
      simp [τ₂, τ₁, hsplit, length_arrOf]
    obtain ⟨split', hsplit₃⟩ := exists_arrOf_of_length hsplitLen
    let τ₄ := τ₃.setVar "phase2Cursor" (i + 1)
    have rinc : Run B (inc "phase2Cursor") τ₃ τ₄ 4 := by
      have hvar : (Expr.var "phase2Cursor").evalB B τ₃ = some i := by
        rw [evalB_var_iff]
        exact ⟨hcursor₃.symm, by rw [hcursor₃]; exact hiB⟩
      have heval : (Expr.add (.var "phase2Cursor") (.lit 1)).evalB B τ₃ =
          some (i + 1) := evalB_bin hvar (evalB_lit honeB) hnextB
      simpa [τ₄, inc] using (Run.assign heval)
    have rbody : Run B exceptionScanBody τ τ₄
        (300 * (offset (i + 1) - offset i + 1) + 24) := by
      have h := Run.seq
        (Run.ite_true (d := .skip) htest
          (Run.seq rtoken (Run.seq rt rstep))) rinc
      exact h.mono (by norm_num [exceptionScanBody, seqs, Cond.size, Expr.size]; omega)
    refine ⟨τ₄, ?_, ?_, by simp [τ₄, hcursor]⟩
    · simpa [hcursor] using rbody
    refine ⟨i + 1, nextCount,
      refinedLabel
        (activeTargets target (setFlag E) (offset i) (offset (i + 1)))
        label nextSplit,
      nextSize, nextStamp, nextCounts, marked', touched', split',
      by omega, by simp [τ₄],
      by simpa [τ₄] using hn₃,
      by simpa [τ₄] using hnextCount, hnextLe,
      by simpa [τ₄] using hoff₃,
      by simpa [τ₄] using htarget₃,
      by simpa [τ₄] using hactiveA₃,
      by simpa [τ₄] using hactiveE₃,
      by simpa [τ₄, scanSample, hiA] using hsample₃,
      by simpa [τ₄] using hlabel₃,
      by simpa [τ₄] using hsize₃,
      by simpa [τ₄] using hstamp₃,
      by simpa [τ₄] using hcounts₃,
      by simpa [τ₄] using hmarked₃,
      by simpa [τ₄] using htouched₃,
      by simpa [τ₄] using hsplit₃,
      hstampLe₃, hcountsZero₃, hnewSizes, hnewOccupied,
      by simpa [scanSample, hiA] using hclassify₃⟩
  · have htest : (Cond.eq (.get "activeA" (.var "phase2Cursor"))
        (.lit 1)).evalB B τ = some false := by
      simpa [setFlag, hiA] using evalB_condEq hget (evalB_lit honeB)
    let τ₁ := τ.setVar "phase2Cursor" (i + 1)
    have rinc : Run B (inc "phase2Cursor") τ τ₁ 4 := by
      have hvar : (Expr.var "phase2Cursor").evalB B τ = some i := by
        rw [evalB_var_iff]
        exact ⟨hcursor.symm, by rw [hcursor]; exact hiB⟩
      have heval : (Expr.add (.var "phase2Cursor") (.lit 1)).evalB B τ =
          some (i + 1) := evalB_bin hvar (evalB_lit honeB) hnextB
      simpa [τ₁, inc] using (Run.assign heval)
    have rbody : Run B exceptionScanBody τ τ₁
        (300 * (offset (i + 1) - offset i + 1) + 24) := by
      have h := Run.seq (Run.ite_false
        (c := seqs [
          .assign "token" (.add (.var "phase2Cursor") (.lit 1)),
          .assign "t" (.var "phase2Cursor"),
          exceptionRefinementStep]) htest Run.skip) rinc
      exact h.mono (by norm_num [exceptionScanBody, seqs, Cond.size, Expr.size])
    refine ⟨τ₁, ?_, ?_, by simp [τ₁, hcursor]⟩
    · simpa [hcursor] using rbody
    refine ⟨i + 1, current, label, size, stamp, counts, marked, touched,
      split, by omega, by simp [τ₁],
      by simpa [τ₁] using hn,
      by simpa [τ₁] using hcurrent, hcurrentLe,
      by simpa [τ₁] using hoff,
      by simpa [τ₁] using htarget,
      by simpa [τ₁] using hactiveA,
      by simpa [τ₁] using hactiveE,
      by simpa [τ₁, scanSample, hiA] using hsample,
      by simpa [τ₁] using hlabel,
      by simpa [τ₁] using hsize,
      by simpa [τ₁] using hstamp,
      by simpa [τ₁] using hcounts,
      by simpa [τ₁] using hmarked,
      by simpa [τ₁] using htouched,
      by simpa [τ₁] using hsplit,
      (by intro v hv; exact (hstampLe v hv).trans (by omega)),
      hcountsZero, hsizes, hoccupied,
      by simpa [scanSample, hiA] using hclassify⟩

private lemma offset_prefix_le (offset : ℕ → ℕ) :
    ∀ n, (∀ j < n, offset j ≤ offset (j + 1)) →
      ∀ i ≤ n, offset i ≤ offset n := by
  intro n hmono i hi
  have h : MonotoneOn offset (Set.Icc 0 n) :=
    monotoneOn_of_le_succ Set.ordConnected_Icc (by
      intro j _ hj hnext
      have hjlt : j < n := by
        have hle := (Set.mem_Icc.mp hnext).2
        change j + 1 ≤ n at hle
        omega
      change offset j ≤ offset (j + 1)
      exact hmono j hjlt)
  exact h (by simp only [Set.mem_Icc]; omega)
    (by simp only [Set.mem_Icc]; omega) hi

/-- The source while loop visits all numeric candidate indices.  Its
potential charges each CSR interval exactly once and a fixed amount for
each cursor value. -/
private lemma scanLoop_run
    {B n targetCap : ℕ} {N : ℕ → Finset ℕ}
    {E A W : Finset ℕ} {offset target : ℕ → ℕ} {σ : Env}
    (hE : E ⊆ Finset.range n) (hA : A ⊆ Finset.range n)
    (hW : W ⊆ Finset.range n)
    (hCSR : ∀ i ∈ A, ∀ b ∈ E,
      (b ∈ activeTargets target (setFlag E) (offset i) (offset (i + 1)) ↔
        i ∈ N b))
    (hoffMono : ∀ i < n, offset i ≤ offset (i + 1))
    (hoffRange : ∀ i < n + 1, offset i ≤ targetCap)
    (htargetRange : ∀ i < n, ∀ j, offset i ≤ j → j < offset (i + 1) →
      target j < n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hI : ScanInv n targetCap N E A W offset target σ)
    (hcursor0 : σ.vars "phase2Cursor" = 0) :
    ∃ σ', Run B
        (.while (.lt (.var "phase2Cursor") (.var "n")) exceptionScanBody)
        σ σ' (300 * (offset n - offset 0) + 328 * n + 4) ∧
      ScanInv n targetCap N E A W offset target σ' ∧
      σ'.vars "phase2Cursor" = n := by
  let I := ScanInv n targetCap N E A W offset target
  let Φ : Env → ℕ := fun τ =>
    300 * (offset n - offset (τ.vars "phase2Cursor")) +
      328 * (n - τ.vars "phase2Cursor")
  have hdef : ∀ τ, I τ →
      ∃ v, (Cond.lt (.var "phase2Cursor") (.var "n")).evalB B τ = some v := by
    intro τ hτ
    rcases hτ with ⟨i, _, _, _, _, _, _, _, _, hiLe, hcursor, hn, -⟩
    exact evalB_condLt_vars
      (by rw [hcursor]; exact (hiLe.trans_lt hnB))
      (by rw [hn]; exact hnB)
  have hstep : ∀ τ, I τ →
      (Cond.lt (.var "phase2Cursor") (.var "n")).evalB B τ = some true →
      ∃ τ' K, Run B exceptionScanBody τ τ' K ∧ I τ' ∧
        1 + (Cond.lt (.var "phase2Cursor") (.var "n")).size +
          K + Φ τ' ≤ Φ τ := by
    intro τ hτ hcond
    obtain ⟨τ', rbody, hτ', hcursor'⟩ :=
      scanBody_run hE hA hW hCSR hoffMono hoffRange htargetRange
        hnB htargetCapB honeB hτ (by
          have hlt := lt_of_condLt_true hcond
          rcases hτ with ⟨_, _, _, _, _, _, _, _, _, _, _, hn, -⟩
          simpa [hn] using hlt)
    let i := τ.vars "phase2Cursor"
    have hiLt : i < n := by
      have hlt := lt_of_condLt_true hcond
      rcases hτ with ⟨_, _, _, _, _, _, _, _, _, _, _, hn, -⟩
      simpa [i, hn] using hlt
    have hmono : offset i ≤ offset (i + 1) := hoffMono i hiLt
    have htail : offset (i + 1) ≤ offset n :=
      offset_prefix_le offset n hoffMono (i + 1) (by omega)
    have hleft : offset n - offset i =
        (offset (i + 1) - offset i) +
          (offset n - offset (i + 1)) := by omega
    refine ⟨τ',
      300 * (offset (i + 1) - offset i + 1) + 24,
      ?_, hτ', ?_⟩
    · simpa [i] using rbody
    · dsimp [Φ]
      simp only [show τ.vars "phase2Cursor" = i from rfl] at hcursor' ⊢
      rw [hcursor', hleft]
      omega
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential I Φ hdef hstep hI
  have hcursorFinal : σ'.vars "phase2Cursor" = n := by
    have hge := le_of_condLt_false hfalse
    rcases hI' with ⟨i, _, _, _, _, _, _, _, _, hiLe, hcursor, hn, -⟩
    omega
  have hΦStart : Φ σ = 300 * (offset n - offset 0) + 328 * n := by
    simp [Φ, hcursor0]
  have hΦFinal : Φ σ' = 0 := by
    simp [Φ, hcursorFinal]
  refine ⟨σ', hrun.mono ?_, hI', hcursorFinal⟩
  rw [hΦStart, hΦFinal] at hpay
  norm_num [Cond.size, Expr.size] at hpay
  omega

/-- The fixed phase-two source scans all candidate indices once.  It starts
from a supplied compact exception partition; clearing the stamp array here
makes its prior contents irrelevant.  The exact source cost telescopes over
CSR intervals and is bounded by a linear expression in `n` and target
capacity. -/
lemma exceptionRefinementScan_run
    {B n targetCap base : ℕ} {σ : Env}
    {N : ℕ → Finset ℕ} {E A W : Finset ℕ}
    {label size offset target stamp counts marked touched split : ℕ → ℕ}
    (hE : E ⊆ Finset.range n) (hA : A ⊆ Finset.range n)
    (hW : W ⊆ Finset.range n)
    (hclassify : ∀ b ∈ E, ∀ b' ∈ E,
      (label b = label b' ↔ trace N W b = trace N W b'))
    (hCSR : ∀ i ∈ A, ∀ b ∈ E,
      (b ∈ activeTargets target (setFlag E) (offset i) (offset (i + 1)) ↔
        i ∈ N b))
    (hn : σ.vars "n" = n) (hbase : σ.vars "classCount" = base)
    (hoff : σ.arrs "off" = arrOf (n + 1) offset)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hactiveA : σ.arrs "activeA" = arrOf n (setFlag A))
    (hactiveE : σ.arrs "exceptionFlags" = arrOf n (setFlag E))
    (hsample : σ.arrs "sampleFlags" = arrOf n (setFlag W))
    (hlabel : σ.arrs "classB" = arrOf n label)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hcounts : σ.arrs "markedCount" = arrOf n counts)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hsplit : σ.arrs "split" = arrOf n split)
    (hbaseN : base ≤ n)
    (hoffMono : ∀ i < n, offset i ≤ offset (i + 1))
    (hoffRange : ∀ i < n + 1, offset i ≤ targetCap)
    (htargetRange : ∀ i < n, ∀ j, offset i ≤ j → j < offset (i + 1) →
      target j < n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hcountsZero : ∀ q < n, counts q = 0)
    (hsizes : ClassSizes n base (setFlag E) label size)
    (hoccupied : LabelsOccupyPrefix base label E) :
    ∃ σ' current finalLabel finalSize finalStamp finalCounts
      finalMarked finalTouched finalSplit,
      Run B exceptionRefinementScan σ σ'
        (300 * (offset n - offset 0) + 339 * n + 12) ∧
      Run B exceptionRefinementScan σ σ'
        (339 * (n + targetCap + 1)) ∧
      σ'.vars "phase2Cursor" = n ∧
      σ'.vars "n" = n ∧
      σ'.vars "classCount" = current ∧ current ≤ n ∧
      σ'.arrs "off" = arrOf (n + 1) offset ∧
      σ'.arrs "tgt" = arrOf targetCap target ∧
      σ'.arrs "activeA" = arrOf n (setFlag A) ∧
      σ'.arrs "exceptionFlags" = arrOf n (setFlag E) ∧
      σ'.arrs "sampleFlags" = arrOf n
        (setFlag (phase2Scan N E
          ((List.range n).filter fun a => a ∈ A) W)) ∧
      σ'.arrs "classB" = arrOf n finalLabel ∧
      σ'.arrs "classSize" = arrOf n finalSize ∧
      σ'.arrs "stamp" = arrOf n finalStamp ∧
      σ'.arrs "markedCount" = arrOf n finalCounts ∧
      σ'.arrs "marked" = arrOf n finalMarked ∧
      σ'.arrs "touched" = arrOf n finalTouched ∧
      σ'.arrs "split" = arrOf n finalSplit ∧
      (∀ v < n, finalStamp v ≤ n) ∧
      (∀ q < n, finalCounts q = 0) ∧
      ClassSizes n current (setFlag E) finalLabel finalSize ∧
      LabelsOccupyPrefix current finalLabel E ∧
      (∀ b ∈ E, ∀ b' ∈ E,
        (finalLabel b = finalLabel b' ↔
          trace N (phase2Scan N E
            ((List.range n).filter fun a => a ∈ A) W) b =
            trace N (phase2Scan N E
              ((List.range n).filter fun a => a ∈ A) W) b')) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (∀ a, a ∉ exceptionRefinementScan.warrs →
        σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ∉ exceptionRefinementScan.wvars →
        σ'.vars x = σ.vars x) := by
  obtain ⟨σ₁, stamp₀, rclear, hstamp₁, hstampZero⟩ :=
    clearArray_run hstamp hn (by decide) hnB
  let σ₂ := σ₁.setVar "phase2Cursor" 0
  have rinit : Run B (.assign "phase2Cursor" (.lit 0)) σ₁ σ₂ 2 := by
    simpa [σ₂] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hn₂ : σ₂.vars "n" = n := by
    rw [show σ₂.vars "n" = σ₁.vars "n" by simp [σ₂]]
    rw [rclear.frame_var "n" (by decide)]
    exact hn
  have hbase₂ : σ₂.vars "classCount" = base := by
    rw [show σ₂.vars "classCount" = σ₁.vars "classCount" by simp [σ₂]]
    rw [rclear.frame_var "classCount" (by decide)]
    exact hbase
  have harray₂ (a : String) (ha : a ≠ "stamp") :
      σ₂.arrs a = σ.arrs a := by
    rw [show σ₂.arrs a = σ₁.arrs a by simp [σ₂]]
    exact rclear.frame_arr a (by
      simp [clearArray, seqs, inc, Com.warrs, ha])
  have hI₂ : ScanInv n targetCap N E A W offset target σ₂ := by
    refine ⟨0, base, label, size, stamp₀, counts, marked, touched,
      split, by omega, by simp [σ₂], hn₂, hbase₂, hbaseN,
      (harray₂ "off" (by decide)).trans hoff,
      (harray₂ "tgt" (by decide)).trans htarget,
      (harray₂ "activeA" (by decide)).trans hactiveA,
      (harray₂ "exceptionFlags" (by decide)).trans hactiveE,
      by simpa [scanSample] using
        (harray₂ "sampleFlags" (by decide)).trans hsample,
      (harray₂ "classB" (by decide)).trans hlabel,
      (harray₂ "classSize" (by decide)).trans hsize,
      by simpa [σ₂] using hstamp₁,
      (harray₂ "markedCount" (by decide)).trans hcounts,
      (harray₂ "marked" (by decide)).trans hmarked,
      (harray₂ "touched" (by decide)).trans htouched,
      (harray₂ "split" (by decide)).trans hsplit,
      (by intro v hv; exact (hstampZero v hv).le),
      hcountsZero, hsizes, hoccupied,
      by simpa [scanSample] using hclassify⟩
  obtain ⟨σ₃, rloop, hI₃, hcursor₃⟩ :=
    scanLoop_run hE hA hW hCSR hoffMono hoffRange htargetRange
      hnB htargetCapB honeB hI₂ (by simp [σ₂])
  rcases hI₃ with ⟨i, current, finalLabel, finalSize, finalStamp,
    finalCounts, finalMarked, finalTouched, finalSplit,
    _hiLe, hi₃, hn₃, hcurrent₃, hcurrentLe, hoff₃, htarget₃,
    hactiveA₃, hactiveE₃, hsample₃, hlabel₃, hsize₃,
    hstamp₃, hcounts₃, hmarked₃, htouched₃, hsplit₃,
    hstampLe₃, hcountsZero₃, hfinalSizes, hfinalOccupied,
    hfinalClassify⟩
  have hiEq : i = n := by omega
  have hprecise : Run B exceptionRefinementScan σ σ₃
      (300 * (offset n - offset 0) + 339 * n + 12) := by
    have h := Run.seq rclear (Run.seq rinit rloop)
    exact h.mono (by omega)
  have hlinear : Run B exceptionRefinementScan σ σ₃
      (339 * (n + targetCap + 1)) := by
    have hoffN : offset n ≤ targetCap := hoffRange n (by omega)
    exact hprecise.mono (by omega)
  refine ⟨σ₃, current, finalLabel, finalSize, finalStamp,
    finalCounts, finalMarked, finalTouched, finalSplit,
    hprecise, hlinear, hcursor₃, hn₃, hcurrent₃, hcurrentLe,
    hoff₃, htarget₃, hactiveA₃, hactiveE₃, ?_, hlabel₃,
    hsize₃, hstamp₃, hcounts₃, hmarked₃, htouched₃, hsplit₃,
    ?_, hcountsZero₃, hfinalSizes, hfinalOccupied,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hiEq, scanSample_eq_phase2Scan] using hsample₃
  · intro v hv
    simpa [hiEq] using hstampLe₃ v hv
  · simpa [hiEq, scanSample_eq_phase2Scan] using hfinalClassify
  · exact hprecise.frame_inp (by decide)
  · exact hprecise.out_eq (by decide)
  · intro a ha
    exact hprecise.frame_arr a ha
  · intro x hx
    exact hprecise.frame_var x hx

end Lax457868Proofs.ExceptionRefinementScan
