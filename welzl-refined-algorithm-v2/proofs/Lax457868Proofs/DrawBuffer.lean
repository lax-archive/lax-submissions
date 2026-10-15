import Mathlib.Tactic
import Lax457868Proofs.IndexedDrawRam
import Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

/-!
One source command performs a capped indexed draw and, only when that draw
succeeds, appends its value to the occupied prefix of `sampleDraws`. The
source is fixed for every domain, counter, and draw value; repeated values are
stored again, as required for sampling with replacement.
-/

namespace Lax457868Proofs.DrawBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.IndexedDrawRam
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FairBitRam
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

/-- Append the looked-up value when the selector's success flag is one. -/
def appendDrawIfFound : Com :=
  .ite (.eq (.var "drawFound") (.lit 1))
    (seqs [
      .store "sampleDraws" (.var "drawCount") (.var "drawVertex"),
      inc "drawCount"])
    .skip

/-- Fixed code for one counted indexed draw followed by its guarded buffer
append. The append executes only after `indexedDrawLookup` has succeeded. -/
def countedIndexedDrawAppend : Com :=
  seqs [seqs [countedRejectionSelector, indexedDrawLookup], appendDrawIfFound]

private lemma appendDrawIfFound_run_success {B d cap value : ℕ}
    {σ : Env} {draws : ℕ → ℕ}
    (hcount : σ.vars "drawCount" = d)
    (hbuf : σ.arrs "sampleDraws" = arrOf cap draws)
    (hfound : σ.vars "drawFound" = 1)
    (hvertex : σ.vars "drawVertex" = value)
    (hcapacity : d < cap) (hnextB : d + 1 < B)
    (hvalueB : value < B) (honeB : 1 < B) :
    ∃ σ', Run B appendDrawIfFound σ σ' 12 ∧
      σ'.arrs "sampleDraws" = arrOf cap (upd draws d value) ∧
      σ'.vars "drawCount" = d + 1 ∧
      (∀ a, a ≠ "sampleDraws" → σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ≠ "drawCount" → σ'.vars x = σ.vars x) := by
  let σ₁ := σ.setArr "sampleDraws" d value
  let σ₂ := σ₁.setVar "drawCount" (d + 1)
  have hdB : d < B := by omega
  have hidx : (Expr.var "drawCount").evalB B σ = some d :=
    by
      have hbound : σ.vars "drawCount" < B := by simpa [hcount] using hdB
      simpa [hcount] using (evalB_var (x := "drawCount") hbound)
  have hval : (Expr.var "drawVertex").evalB B σ = some value :=
    by
      have hbound : σ.vars "drawVertex" < B := by simpa [hvertex] using hvalueB
      simpa [hvertex] using (evalB_var (x := "drawVertex") hbound)
  have hstore0 : Run B
      (.store "sampleDraws" (.var "drawCount") (.var "drawVertex")) σ σ₁ 3 := by
    apply Run.store hidx hval
    simpa [hbuf] using hcapacity
  have hstore : Run B
      (.store "sampleDraws" (.var "drawCount") (.var "drawVertex")) σ σ₁ 4 :=
    hstore0.mono (by decide)
  have hcount₁ : σ₁.vars "drawCount" = d := by simp [σ₁, hcount]
  have hincEval :
      (Expr.add (.var "drawCount") (.lit 1)).evalB B σ₁ = some (d + 1) := by
    have hvar : (Expr.var "drawCount").evalB B σ₁ = some d := by
      have hbound : σ₁.vars "drawCount" < B := by rw [hcount₁]; omega
      simpa [hcount₁] using (evalB_var (x := "drawCount") hbound)
    have hbin := evalB_bin (op := Bop.add) hvar (evalB_lit honeB)
      (by simpa [Bop.apply] using hnextB)
    simpa [Bop.apply] using hbin
  have hinc : Run B (inc "drawCount") σ₁ σ₂ 4 := by
    simpa [inc, σ₂] using (Run.assign hincEval)
  have hbody : Run B
      (seqs [
        .store "sampleDraws" (.var "drawCount") (.var "drawVertex"),
        inc "drawCount"]) σ σ₂ 8 := by
    simpa [seqs] using Run.seq hstore hinc
  have hcond : (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ = some true := by
    have hB : 1 < B := by omega
    rw [evalB_condEq (evalB_var (by simpa [hfound] using hB))
      (evalB_lit (by omega : 1 < B))]
    simp [hfound]
  have hrun : Run B appendDrawIfFound σ σ₂ 12 := by
    simpa [appendDrawIfFound] using (Run.ite_true hcond hbody)
  refine ⟨σ₂, hrun, ?_, ?_, ?_, ?_⟩
  · simp [σ₂, σ₁, hbuf, set_arrOf_eq_upd]
  · simp [σ₂]
  · intro a ha
    simp [σ₂, σ₁, ha]
  · intro x hx
    have hincFrame := hinc.frame_var x (by simp [inc, Com.wvars, hx])
    have hstoreFrame := hstore.frame_var x (by simp [Com.wvars])
    exact hincFrame.trans hstoreFrame

private lemma appendDrawIfFound_run_failure {B : ℕ} {σ : Env}
    (hfound : σ.vars "drawFound" = 0) (hB : 1 < B) :
    ∃ σ', Run B appendDrawIfFound σ σ' 12 ∧ σ' = σ := by
  have hcond : (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var (by simpa [hfound] using (by omega : 0 < B)))
      (evalB_lit hB)]
    simp [hfound]
  have hskip : Run B .skip σ σ 1 := Run.skip
  have hrun : Run B appendDrawIfFound σ σ 12 := by
    change Run B
      (.ite (.eq (.var "drawFound") (.lit 1))
        (seqs [
          .store "sampleDraws" (.var "drawCount") (.var "drawVertex"),
          inc "drawCount"]) .skip) σ σ 12
    have h : Run B
        (.ite (.eq (.var "drawFound") (.lit 1))
          (seqs [
            .store "sampleDraws" (.var "drawCount") (.var "drawVertex"),
            inc "drawCount"]) .skip) σ σ
        (1 + (Cond.eq (.var "drawFound") (.lit 1)).size + 1) :=
      Run.ite_false hcond hskip
    simpa [appendDrawIfFound] using h.mono (by decide)
  exact ⟨σ, hrun, rfl⟩

/-- Execute one actual counted indexed draw and append its selected domain
value at `sampleDraws[drawCount]` exactly on success. Capacity is sufficient
for that store, the counter increment fits in one word, and domain entries
fit in one word. Repetitions are retained. On exhaustion the buffer and count
are unchanged. The extra append code has a derived bound of 12 source steps
(the success branch costs the equality test, store, and increment; failure is
cheaper). -/
lemma countedIndexedDrawAppend_run_tape {B n v m domainCap t drawCap drawCount : ℕ}
    {σ : Env} {g domain draws : ℕ → ℕ} {rest : List ℕ}
    (tape : BitTape m t) (hm : 0 < m)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hdomain : σ.arrs "drawDomain" = arrOf domainCap domain)
    (hmCap : m ≤ domainCap)
      (hvalueB : ∀ i < m, domain i < B)
    (hdraws : σ.arrs "sampleDraws" = arrOf drawCap draws)
    (hcount : σ.vars "drawCount" = drawCount)
    (hcapacity : drawCount < drawCap)
    (hnextB : drawCount + 1 < B)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = Nat.clog 2 m)
    (hmod : σ.vars "drawModulus" = m)
    (hcap : σ.vars "drawCap" = t)
    (hinp : σ.inp = flattenBitBlocks tape ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B) (hnB : n < B) (htwoB : 2 < B)
    (htB : t < B) (hmB : m < B) (honeB : 1 < B) :
    ∃ (σ' : Env) (g' : ℕ → ℕ),
      Run B countedIndexedDrawAppend σ σ'
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 31) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧
      ((selectBitIndexWithCount m hm t tape).1 ≠ none →
        ∃ i, (selectBitIndexWithCount m hm t tape).1 = some i ∧
          σ'.arrs "sampleDraws" = arrOf drawCap (upd draws drawCount (domain i.val)) ∧
          σ'.vars "drawCount" = drawCount + 1) ∧
      ((selectBitIndexWithCount m hm t tape).1 = none →
        σ'.arrs "sampleDraws" = arrOf drawCap draws ∧
        σ'.vars "drawCount" = drawCount ∧
        σ'.vars "drawVertex" = σ.vars "drawVertex") ∧
      σ'.vars "drawUsed" = bitTapeAttemptsUsed m t tape ∧
      σ'.vars "drawFound" =
        (if (selectBitIndexWithCount m hm t tape).1 = none then 0 else 1) ∧
      σ'.inp = flattenBitBlockList
        ((List.ofFn tape).drop (bitTapeAttemptsUsed m t tape)) ++ rest ∧
      σ'.arrs "drawDomain" = arrOf domainCap domain ∧
      (∀ a, a ≠ "key0" → a ≠ "sampleDraws" → σ'.arrs a = σ.arrs a) ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = Nat.clog 2 m ∧
      σ'.vars "drawModulus" = m ∧ σ'.vars "drawCap" = t := by
  obtain ⟨σ₁, g', hdrawRun, hkey₁, hframe₁, hvertex, hvertexFail,
      hused₁, hfound₁, hinp₁, hdomain₁, harrframe₁, hv₁, hL₁, hmod₁,
      hcap₁⟩ := countedIndexedDraw_run_tape tape hm hkey hdomain hmCap hvalueB
      hv hvn hL hmod hcap hinp hpowB hnB htwoB htB hmB
  have hdraws₁ : σ₁.arrs "sampleDraws" = arrOf drawCap draws := by
    exact (harrframe₁ "sampleDraws" (by decide)).trans hdraws
  have hcount₁ : σ₁.vars "drawCount" = drawCount :=
    (hdrawRun.frame_var "drawCount" (by decide)).trans hcount
  by_cases hs : (selectBitIndexWithCount m hm t tape).1 = none
  · have hfoundZero : σ₁.vars "drawFound" = 0 := by simp [hfound₁, hs]
    obtain ⟨σ', happend, rfl⟩ := appendDrawIfFound_run_failure hfoundZero (by omega)
    have hwhole : Run B countedIndexedDrawAppend σ σ'
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 31) := by
      have hseq := Run.seq hdrawRun happend
      simpa [countedIndexedDrawAppend, seqs, Nat.add_assoc] using hseq
    refine ⟨σ', g', hwhole,
      (happend.frame_arr "key0" (by decide)).trans hkey₁, hframe₁,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv₁, hL₁, hmod₁, hcap₁⟩
    · intro hne
      exact (hne hs).elim
    · intro _
      exact ⟨hdraws₁, hcount₁, hvertexFail hs⟩
    · exact (happend.frame_var "drawUsed" (by decide)).trans hused₁
    · simpa [hs] using (happend.frame_var "drawFound" (by decide)).trans hfound₁
    · exact hinp₁
    · exact (happend.frame_arr "drawDomain" (by decide)).trans hdomain₁
    · intro a ha hb
      exact harrframe₁ a ha
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hs
    have hfoundOne : σ₁.vars "drawFound" = 1 := by simp [hfound₁, hs]
    have hvertex' : σ₁.vars "drawVertex" = domain i.val := hvertex i hi
    have hvalue : domain i.val < B := hvalueB i.val i.isLt
    have hcount₁' : σ₁.vars "drawCount" = drawCount := hcount₁
    obtain ⟨σ', happend, hdraws', hcount', harrayframe, hvarframe⟩ :=
      appendDrawIfFound_run_success hcount₁' hdraws₁ hfoundOne hvertex'
        hcapacity hnextB hvalue honeB
    have hwhole : Run B countedIndexedDrawAppend σ σ'
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 31) := by
      have hseq := Run.seq hdrawRun happend
      simpa [countedIndexedDrawAppend, seqs, Nat.add_assoc] using hseq
    refine ⟨σ', g', hwhole,
      (happend.frame_arr "key0" (by decide)).trans hkey₁, hframe₁,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (happend.frame_var "v" (by decide)).trans hv₁,
      (happend.frame_var "L" (by decide)).trans hL₁,
      (happend.frame_var "drawModulus" (by decide)).trans hmod₁,
      (happend.frame_var "drawCap" (by decide)).trans hcap₁⟩
    · intro _
      exact ⟨i, hi, hdraws', hcount'⟩
    · intro hnone
      exact (hs hnone).elim
    · exact (happend.frame_var "drawUsed" (by decide)).trans hused₁
    · simpa [hs] using (happend.frame_var "drawFound" (by decide)).trans hfound₁
    · exact (happend.frame_inp (by decide)).trans hinp₁
    · exact (happend.frame_arr "drawDomain" (by decide)).trans hdomain₁
    · intro a ha hb
      exact (harrayframe a hb).trans (harrframe₁ a ha)

end Lax457868Proofs.DrawBuffer
