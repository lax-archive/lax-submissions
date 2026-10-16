import Mathlib.Tactic
import Lax457868Proofs.RepairClassOffsets
import Lax457868Proofs.RepairTrialCheck
import Lax457868Proofs.RepairDomainSource
import Lax457868Proofs.ClassBucketDomain
import Lax457868Proofs.SamplerPhases
import Lax457868Proofs.SamplePacking
import Lax457868Proofs.ExceptionRefinementStep
import Lax457868Proofs.ExceptionPhaseSource
import Lax457868Proofs.SourceRenaming
import Lax457868Proofs.ReusedOriginal.Construction.RadixEight

/-! Execute the fixed local-repair trace check over the selected runtime
class slice. The trace of `repairB` is collected once; every other member is
then read from the actual `ord` slice and checked with the degree-local row
checker, which clears its row marks before the next iteration. -/

namespace Lax457868Proofs.RepairClassScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding Lax11Proofs.CC
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.RepairDomainSource
open Lax457868Proofs.RepairClassOffsets
open Lax457868Proofs.RepairTrialCheck
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight

/-- The one-time collector uses private desired-trace storage. -/
def trialDesiredCollectNames : Names :=
  neighborhoodNames "trialActive" "trialDesiredMarks" "trialDesiredList"
    "trialDesiredLen"

def collectDesiredTrace : Com :=
  collectNeighborhoodAt trialDesiredCollectNames "repairB" "trialDesiredLen"

/-- Clear exactly the desired entries written by the one-time collector. -/
def trialDesiredClearNames : Names :=
  repairClearNames "trialDesiredMarks" "trialDesiredList" "trialDesiredLen"

def clearDesiredTrace : Com :=
  renameCom trialDesiredClearNames (markDrawArrayWith 0)

/-- One selected class slot: load its vertex, skip the distinguished vertex,
and otherwise run the checked collect/compare/clear operation. -/
def repairClassScanBody : Com :=
  seqs [
    .assign "trialVertex" (.get "ord" (.var "repairScanCursor")),
    .ite (.eq (.var "trialVertex") (.var "repairB")) .skip
      (seqs [
        collectCheckAndClearTrialRow,
        .ite (.eq (.var "trialTraceEqual") (.lit 1))
          (.assign "repairScanSuccess" (.lit 0)) .skip]),
    inc "repairScanCursor"]

/-- Scan exactly the class interval returned by `repairClassLookup_run`.
The success flag starts true and is lowered whenever another row has the
desired trace. -/
def repairClassScanLoop : Com :=
  seqs [
    .assign "repairScanSuccess" (.lit 1),
    .assign "repairScanCursor" (.var "repairStart"),
    .while (.lt (.var "repairScanCursor") (.var "repairStop"))
      repairClassScanBody]

/-- Complete one local-repair class scan and restore its two touched mark
arrays. -/
def repairClassScanSource : Com :=
  seqs [collectDesiredTrace, repairClassScanLoop, clearDesiredTrace]

/-- The runtime lookup plus the scan. This wrapper deliberately uses the
existing source lookup, so the scan bounds are the actual class slice in
`ord`, not a separately supplied class list. -/
def repairClassLookupAndScan : Com :=
  seqs [repairClassLookup, repairClassScanSource]

/-- One loop iteration pays the actual degree of its `ord` vertex.  The
constant covers the checked row collector, the equality test, and cursor
update; it is summed over the selected slice below. -/
def repairClassSlotWeight (x : List ℕ) (ord : ℕ → ℕ) (i : ℕ) : ℕ :=
  90 * (offset x (ord i + 1) - offset x (ord i)) + 70

/-- Remaining degree-local work in the fixed class slice. -/
def repairClassPotential (stop cursor : ℕ) (weight : ℕ → ℕ) : ℕ :=
  if cursor < stop then
    weight cursor + repairClassPotential stop (cursor + 1) weight
  else 0
termination_by stop - cursor
decreasing_by omega

lemma repairClassPotential_step {stop cursor : ℕ} {weight : ℕ → ℕ}
    (h : cursor < stop) :
    repairClassPotential stop cursor weight =
      weight cursor + repairClassPotential stop (cursor + 1) weight := by
  rw [repairClassPotential.eq_1]
  simp only [h, if_pos]

/-- In graph notation, the once-collected desired trace is the neighborhood
of `b` restricted to the sample represented by the active flags. -/
lemma desiredTrace_eq_numericTrace
    {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (W : Finset ℕ)
    (hW : W ⊆ Finset.range n) {b : ℕ} (hb : b < n) :
    activeTargets (target x) (setFlag W) (offset x b) (offset x (b + 1)) =
      trace (numericNeighborhood G) W b := by
  rw [activeTargets_eq_numericNeighborhood_inter hx W b hb]
  simp [trace]

/-- The desired trace is represented by the one-time CSR collection. -/
lemma collectDesiredTrace_run
    {B n targetCap b : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {σ : Env} {active desiredMarks desiredList : ℕ → ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hrepairB : σ.vars "repairB" = b)
    (hn : σ.vars "n" = n)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs "trialActive" = arrOf n active)
    (hmarks : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0))
    (hlist : σ.arrs "trialDesiredList" = arrOf n desiredList)
    (hb : b < n) (hactiveB : ∀ v < n, active v < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B) :
    ∃ σ' marks' list',
      Run B collectDesiredTrace σ σ'
        (54 * (offset x (b + 1) - offset x b) + 22) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n marks' ∧
      σ'.arrs "trialDesiredList" = arrOf n list' ∧
      σ'.vars "trialDesiredLen" =
        (activeTargets (target x) active
          (offset x b) (offset x (b + 1))).card ∧
      PrefixEnumerates
        (activeTargets (target x) active
          (offset x b) (offset x (b + 1))).card list'
        (activeTargets (target x) active
          (offset x b) (offset x (b + 1))) ∧
      (∀ v < n, marks' v = 1 ↔ v ∈
        activeTargets (target x) active
          (offset x b) (offset x (b + 1))) ∧
      (∀ v < n, marks' v ≤ 1) ∧
      σ'.arrs "trialActive" = σ.arrs "trialActive" ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.arrs "off" = σ.arrs "off" ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hvertexNames : "repairB" ≠ "token" ∧
      "repairB" ≠ "trialDesiredLen" ∧ "repairB" ≠ "j" ∧
      "repairB" ≠ "jend" := by decide
  have hlenNames : "trialDesiredLen" ≠ "token" ∧
      "trialDesiredLen" ≠ "j" ∧ "trialDesiredLen" ≠ "jend" ∧
      "trialDesiredLen" ≠ "n" := by decide
  have h := collectNeighborhoodAt_run trialDesiredCollectNames "repairB"
    "trialActive" "trialDesiredMarks" "trialDesiredList" "trialDesiredLen"
    (by decide) (by decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    (by simp [trialDesiredCollectNames, neighborhoodNames] <;> decide)
    hx htargetCap hrepairB hn hoff htarget hactive hmarks hlist hb
    hactiveB hn1B htargetCapB
  rcases h with ⟨σ', marks', list', hrun, hm, hl, hd, hen, hmem, h01,
    hactive', htarget', hj, htoken, hin, hout⟩
  have hoff' : σ'.arrs "off" = σ.arrs "off" :=
    hrun.frame_arr "off" (by
      simp [collectDesiredTrace, trialDesiredCollectNames,
        neighborhoodNames, collectNeighborhoodAt, prepareNeighborAt,
        renameCom, collectNeighborBody, seqs, inc, Com.warrs] <;> decide)
  have hdomain' : σ'.arrs "drawDomain" = σ.arrs "drawDomain" :=
    hrun.frame_arr "drawDomain" (by
      simp [collectDesiredTrace, trialDesiredCollectNames,
        neighborhoodNames, collectNeighborhoodAt, prepareNeighborAt,
        renameCom, collectNeighborBody, seqs, inc, Com.warrs] <;> decide)
  have hmodulus' : σ'.vars "drawModulus" = σ.vars "drawModulus" :=
    hrun.frame_var "drawModulus" (by
      simp [collectDesiredTrace, trialDesiredCollectNames,
        neighborhoodNames, collectNeighborhoodAt, prepareNeighborAt,
        renameCom, collectNeighborBody, seqs, inc, Com.wvars] <;> decide)
  exact ⟨σ', marks', list', hrun, hm, hl, hd, hen, hmem, h01,
    hactive'.trans hactive.symm, htarget', hoff', hdomain', hmodulus', hin, hout⟩

/-- Touched cleanup restores the desired-mark scratch array for the next
trial without scanning all vertices. -/
lemma clearDesiredTrace_run
    {B n h : ℕ} {σ : Env} {marks list : ℕ → ℕ} {T : Finset ℕ}
    (hn : σ.vars "n" = n)
    (hlen : σ.vars "trialDesiredLen" = h)
    (hmarks : σ.arrs "trialDesiredMarks" = arrOf n marks)
    (hlist : σ.arrs "trialDesiredList" = arrOf n list)
    (henum : PrefixEnumerates h list T)
    (hTrange : T ⊆ Finset.range n)
    (hmarks01 : ∀ v < n, marks v ≤ 1)
    (hmarksMem : ∀ v < n, marks v = 1 ↔ v ∈ T)
    (hnB : n < B) :
    ∃ σ', Run B clearDesiredTrace σ σ' (12 * h + 6) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.vars "repairClearCursor" = h ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σ', hrun, hz, hc, hin, hout⟩ :=
    clearNeighborhoodSupport_run trialDesiredClearNames
      "trialDesiredMarks" "trialDesiredList" "trialDesiredLen"
      (by simp [trialDesiredClearNames, repairClearNames] <;> decide)
      (by simp [trialDesiredClearNames, repairClearNames] <;> decide)
      (by simp [trialDesiredClearNames, repairClearNames] <;> decide)
      (by simp [trialDesiredClearNames, repairClearNames] <;> decide)
      (by simp [trialDesiredClearNames, repairClearNames] <;> decide)
      hn hlen hmarks hlist henum hTrange hmarks01 hmarksMem hnB
  exact ⟨σ', by simpa [clearDesiredTrace, trialDesiredClearNames,
    repairClearNames] using hrun, hz, hc, hin, hout⟩

/-- The source cost of testing one non-distinguished row, including loading
the slot, the equality branch, and cursor increment. -/
def repairClassMemberCost (degree rowCard : ℕ) : ℕ :=
  54 * degree + 22 + 36 * rowCard + 26 + 15

/-- A row's actual checker budget is degree local: duplicate CSR targets can
only decrease the number of selected row entries. -/
lemma repairClassMemberCost_le (degree rowCard : ℕ)
    (hrow : rowCard ≤ degree) :
    repairClassMemberCost degree rowCard ≤ 90 * degree + 63 := by
  dsimp [repairClassMemberCost]
  omega

/-- One checked loop iteration loads an actual `ord` entry. It skips the
distinguished vertex and otherwise invokes the concrete CSR row checker.
The extra 17 steps are the slot load, branch tests, possible flag update,
and cursor increment. The arbitrary difference buffer is recovered from its
preserved runtime length after the row check. -/
lemma repairClassScanBody_run
    {B n targetCap b v i d : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {σ : Env} {active ord rowMarks rowList desiredMarks diffBuffer : ℕ → ℕ}
    {T : Finset ℕ} {success : ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hcursor : σ.vars "repairScanCursor" = i)
    (hrepairB : σ.vars "repairB" = b)
    (hsuccess : σ.vars "repairScanSuccess" = success)
    (hn : σ.vars "n" = n)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs "trialActive" = arrOf n active)
    (hrowMarks : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hrowList : σ.arrs "trialRowList" = arrOf n rowList)
    (hdesiredLen : σ.vars "trialDesiredLen" = d)
    (hdesiredMarks : σ.arrs "trialDesiredMarks" = arrOf n desiredMarks)
    (hdiffList : σ.arrs "trialDiffList" = arrOf n diffBuffer)
    (hdesiredMarks01 : ∀ w < n, desiredMarks w ≤ 1)
    (hdesiredMarksMem : ∀ w < n, desiredMarks w = 1 ↔ w ∈ T)
    (hTrange : T ⊆ Finset.range n)
    (hd : d = T.card)
    (hi : i < n) (hv : ord i = v) (hb : b < n) (hvb : v < n)
    (hactiveB : ∀ w < n, active w < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' rowList' diffBuffer',
      Run B repairClassScanBody σ σ'
        (54 * (offset x (v + 1) - offset x v) + 22 +
          36 * (activeTargets (target x) active (offset x v)
            (offset x (v + 1))).card + 44) ∧
      σ'.vars "repairScanSuccess" =
        (if v = b then success else if
          decide (activeTargets (target x) active (offset x v) (offset x (v + 1)) = T)
          then 0 else success) ∧
      σ'.vars "repairScanCursor" = i + 1 ∧
      σ'.vars "trialVertex" = v ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n desiredMarks ∧
      σ'.arrs "trialRowList" = arrOf n rowList' ∧
      σ'.arrs "trialDiffList" = arrOf n diffBuffer' ∧
      σ'.arrs "trialActive" = arrOf n active ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" := by
  have hiB : i < B := hi.trans hnB
  have hvB : v < B := hvb.trans hnB
  have hget : (Expr.get "ord" (.var "repairScanCursor")).evalB B σ =
      some v := by
    apply evalB_get (evalB_var (by simpa [hcursor] using hiB))
    · rw [hord, hcursor, getElem?_arrOf ord hi]
      exact congrArg some hv
    · exact hvB
  let σ₁ := σ.setVar "trialVertex" v
  have rload : Run B (.assign "trialVertex"
      (.get "ord" (.var "repairScanCursor"))) σ σ₁ 3 := by
    simpa [σ₁, Expr.size] using (Run.assign hget)
  have hvertex₁ : σ₁.vars "trialVertex" = v := by simp [σ₁]
  have hrepairB₁ : σ₁.vars "repairB" = b := by simp [σ₁, hrepairB]
  have hsuccess₁ : σ₁.vars "repairScanSuccess" = success := by
    simp [σ₁, hsuccess]
  have hvertexEval : (Expr.var "trialVertex").evalB B σ₁ = some v := by
    rw [evalB_var_iff]
    exact ⟨hvertex₁.symm, hvB⟩
  have hrepairBEval : (Expr.var "repairB").evalB B σ₁ = some b := by
    rw [evalB_var_iff]
    exact ⟨hrepairB₁.symm, by simpa [hrepairB₁] using hb.trans hnB⟩
  have houter : (Cond.eq (.var "trialVertex") (.var "repairB")).evalB B σ₁ =
      some (v == b) := evalB_condEq hvertexEval hrepairBEval
  let τ := σ₁.setVar "repairScanCursor" (i + 1)
  have rinc : Run B (inc "repairScanCursor") σ₁ τ 4 := by
    have hiAddB : i + 1 < B := by omega
    have heval : (Expr.add (.var "repairScanCursor") (.lit 1)).evalB B σ₁ =
        some (i + 1) := by
      apply evalB_bin
      · rw [evalB_var_iff]
        exact ⟨by simp [σ₁, hcursor], by rw [show σ₁.vars "repairScanCursor" = i from by simp [σ₁, hcursor]]; exact hiB⟩
      · exact evalB_lit honeB
      · exact hiAddB
    simpa [τ, inc] using (Run.assign heval)
  by_cases hvb' : v = b
  · have houter' : (Cond.eq (.var "trialVertex") (.var "repairB")).evalB B σ₁ =
        some true := by simpa [hvb'] using houter
    have rskip : Run B (.ite (.eq (.var "trialVertex") (.var "repairB"))
        .skip (seqs [collectCheckAndClearTrialRow,
          .ite (.eq (.var "trialTraceEqual") (.lit 1))
            (.assign "repairScanSuccess" (.lit 0)) .skip])) σ₁ σ₁ 5 := by
      simpa [Cond.size, Expr.size] using Run.ite_true houter' Run.skip
    have rbody : Run B repairClassScanBody σ τ 12 := by
      have h := rload.seq (rskip.seq rinc)
      simpa [repairClassScanBody, seqs, τ] using h
    refine ⟨τ, rowList, diffBuffer, rbody.mono (by omega),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [τ, σ₁, hsuccess, hvb']
    · simp [τ]
    · exact hvertex₁
    · simpa [τ, σ₁] using hrowMarks
    · simpa [τ, σ₁] using hdesiredMarks
    · exact hrowList
    · exact hdiffList
    · simpa [τ, σ₁] using hactive
    · simpa [τ, σ₁] using hord
    · simpa [τ, σ₁] using hoff
    · simpa [τ, σ₁] using htarget
    · simp [τ, σ₁]
    · simp [τ, σ₁]
  · have hcheckInput : σ₁.vars "trialVertex" = v := hvertex₁
    obtain ⟨σ₂, rowList₂, rcheck, hequal, hflagLE₂, hmarksZero₂, hdomain₂,
      hmodulus₂, hrowList₂, _hdesired₂, hsample₂, _hactive₂, _hord₂,
      _hrep₂, _hclassB₂, _hclassSize₂⟩ :=
      @collectCheckAndClearTrialRow_run B n d targetCap v G x σ₁ active
        (fun _ => 0) rowList desiredMarks diffBuffer T
        hx htargetCap hcheckInput
        (by simpa [σ₁, hn] using hn)
        (by simpa [σ₁, hoff] using hoff)
        (by simpa [σ₁, htarget] using htarget)
        (by simpa [σ₁, hactive] using hactive)
        (by simpa [σ₁] using hrowMarks)
        hrowList
        (by simpa [σ₁, hdesiredLen] using hdesiredLen)
        (by simpa [σ₁, hdesiredMarks] using hdesiredMarks)
        (by simpa [σ₁] using hdiffList)
        hdesiredMarks01 hdesiredMarksMem hTrange hd hvb hactiveB
        hn1B htargetCapB hnB honeB
    have hflag₂ : σ₂.vars "trialTraceEqual" = 1 ↔
        activeTargets (target x) active (offset x v) (offset x (v + 1)) = T := by
      simpa [hv] using hequal
    let σ₃ := if decide (activeTargets (target x) active
        (offset x v) (offset x (v + 1)) = T) then
      σ₂.setVar "repairScanSuccess" 0 else σ₂
    let test := Cond.eq (.var "trialTraceEqual") (.lit 1)
    have hflagLE : σ₂.vars "trialTraceEqual" ≤ 1 := hflagLE₂
    have hflagBool : (σ₂.vars "trialTraceEqual" == 1) =
        decide (activeTargets (target x) active (offset x v) (offset x (v + 1)) = T) := by
      by_cases heq : activeTargets (target x) active (offset x v) (offset x (v + 1)) = T
      · have honeFlag : σ₂.vars "trialTraceEqual" = 1 := hflag₂.mpr heq
        simp [honeFlag, heq]
      · have hzeroFlag : σ₂.vars "trialTraceEqual" = 0 := by
          have hne1 : σ₂.vars "trialTraceEqual" ≠ 1 := by
            intro h; exact heq (hflag₂.mp h)
          omega
        simp [hzeroFlag, heq]
    have htest : test.evalB B σ₂ = some
        (decide (activeTargets (target x) active (offset x v) (offset x (v + 1)) = T)) := by
      have hflagEval : (Expr.var "trialTraceEqual").evalB B σ₂ =
          some (σ₂.vars "trialTraceEqual") := by
        rw [evalB_var_iff]
        exact ⟨rfl, lt_of_le_of_lt hflagLE (by omega : 1 < B)⟩
      have htest' : test.evalB B σ₂ =
          some (σ₂.vars "trialTraceEqual" == 1) := by
        exact evalB_condEq hflagEval (evalB_lit (by omega : 1 < B))
      rw [htest', hflagBool]
    have hupdate : Run B (.ite test (.assign "repairScanSuccess" (.lit 0))
        .skip) σ₂ σ₃ 6 := by
      by_cases heq : activeTargets (target x) active (offset x v) (offset x (v + 1)) = T
      · have heval : test.evalB B σ₂ = some true := by simpa [heq] using htest
        have ha : Run B (.assign "repairScanSuccess" (.lit 0)) σ₂
            (σ₂.setVar "repairScanSuccess" 0) 2 := by
          simpa using Run.assign (evalB_lit (by omega : 0 < B))
        have hr : Run B (.ite test (.assign "repairScanSuccess" (.lit 0)) .skip)
            σ₂ (σ₂.setVar "repairScanSuccess" 0) 6 := by
          simpa [test, Cond.size, Expr.size] using Run.ite_true heval ha
        simpa [σ₃, heq] using hr
      · have heval : test.evalB B σ₂ = some false := by simpa [heq] using htest
        have hr : Run B (.ite test (.assign "repairScanSuccess" (.lit 0)) .skip)
            σ₂ σ₂ 5 := by
          simpa [test, Cond.size, Expr.size] using Run.ite_false heval Run.skip
        have hs : σ₂.vars "repairScanSuccess" = success := by
          rw [rcheck.frame_var "repairScanSuccess" (by decide)]
          exact hsuccess₁
        simpa [σ₃, heq] using (hr.mono (by omega : 5 ≤ 6))
    let σ₄ := σ₃.setVar "repairScanCursor" (i + 1)
    have hcursor₂ : σ₂.vars "repairScanCursor" = i := by
      rw [rcheck.frame_var "repairScanCursor" (by decide)]
      exact hcursor
    have hsuccess₂ : σ₂.vars "repairScanSuccess" = success := by
      rw [rcheck.frame_var "repairScanSuccess" (by decide)]
      exact hsuccess₁
    have rinc₃ : Run B (inc "repairScanCursor") σ₃ σ₄ 4 := by
      have hcursor₃ : σ₃.vars "repairScanCursor" = i := by
        by_cases heq : activeTargets (target x) active
            (offset x v) (offset x (v + 1)) = T
        · simpa [σ₃, heq] using hcursor₂
        · simpa [σ₃, heq] using hcursor₂
      have heval : (Expr.add (.var "repairScanCursor") (.lit 1)).evalB B σ₃ =
          some (i + 1) := by
        have hiAddB : i + 1 < B := by omega
        apply evalB_bin
        · rw [evalB_var_iff]
          exact ⟨by simpa [hcursor₃], by simpa [hcursor₃] using hiB⟩
        · exact evalB_lit honeB
        · exact hiAddB
      simpa [σ₄, inc] using (Run.assign heval)
    have rbody : Run B repairClassScanBody σ σ₄
        (54 * (offset x (v + 1) - offset x v) + 22 +
          36 * (activeTargets (target x) active (offset x v)
            (offset x (v + 1))).card + 44) := by
      have houterFalse : (Cond.eq (.var "trialVertex") (.var "repairB")).evalB B σ₁ =
          some false := by simpa [hvb'] using houter
      have hinner := rcheck.seq hupdate
      have router : Run B
          (.ite (.eq (.var "trialVertex") (.var "repairB")) .skip
            (seqs [collectCheckAndClearTrialRow,
              .ite (.eq (.var "trialTraceEqual") (.lit 1))
                (.assign "repairScanSuccess" (.lit 0)) .skip]))
          σ₁ σ₃ (4 + (54 * (offset x (v + 1) - offset x v) + 22 +
            36 * (activeTargets (target x) active (offset x v)
              (offset x (v + 1))).card + 26 + 6)) := by
        have hi : Run B (.ite (.eq (.var "trialVertex") (.var "repairB"))
            .skip (seqs [collectCheckAndClearTrialRow,
              .ite (.eq (.var "trialTraceEqual") (.lit 1))
                (.assign "repairScanSuccess" (.lit 0)) .skip])) σ₁ σ₃
            (4 + (54 * (offset x (v + 1) - offset x v) + 22 +
              36 * (activeTargets (target x) active (offset x v)
                (offset x (v + 1))).card + 26 + 6)) := by
          have houterRun := Run.ite_false (c := Com.skip)
            (d := seqs [collectCheckAndClearTrialRow,
              .ite (.eq (.var "trialTraceEqual") (.lit 1))
                (.assign "repairScanSuccess" (.lit 0)) .skip])
            houterFalse hinner
          simpa [seqs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using houterRun
        exact hi.mono (by omega)
      have h := rload.seq (router.seq rinc₃)
      have hcost : 3 + (4 + (54 * (offset x (v + 1) - offset x v) + 22 +
          36 * (activeTargets (target x) active (offset x v) (offset x (v + 1))).card + 26 + 6) + 4) ≤
          54 * (offset x (v + 1) - offset x v) + 22 +
            36 * (activeTargets (target x) active (offset x v) (offset x (v + 1))).card + 44 := by
        omega
      have h' := h.mono (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcost)
      simpa [repairClassScanBody, seqs, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h'
    have hdiffLen : (σ₄.arrs "trialDiffList").length = n := by
      rw [run_array_length_eq rbody "trialDiffList", hdiffList, length_arrOf]
    obtain ⟨diffBuffer', hdiffBuffer'⟩ := exists_arrOf_of_length hdiffLen
    refine ⟨σ₄, rowList₂, diffBuffer', rbody,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T
      · simp [σ₄, σ₃, heq, hvb']
      · simp [σ₄, σ₃, heq, hsuccess₂]
    · simp [σ₄, σ₃, hcursor₂]
    · have hvtx : σ₂.vars "trialVertex" = v := by
        rw [rcheck.frame_var "trialVertex" (by decide)]
        exact hvertex₁
      by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T
      · simp [σ₄, σ₃, hvtx, heq]
      · simp [σ₄, σ₃, hvtx, heq]
    · by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T <;>
        simpa [σ₄, σ₃, heq] using hmarksZero₂
    · by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T
      · simpa [σ₄, σ₃, heq] using
          rcheck.frame_arr "trialDesiredMarks" (by decide) |>.trans hdesiredMarks
      · simpa [σ₄, σ₃, heq] using
          rcheck.frame_arr "trialDesiredMarks" (by decide) |>.trans hdesiredMarks
    · by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T <;>
        simpa [σ₄, σ₃, heq] using hrowList₂
    · exact hdiffBuffer'
    · by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T
      · simpa [σ₄, σ₃, heq] using
          (rcheck.frame_arr "trialActive" (by decide)).trans hactive
      · simpa [σ₄, σ₃, heq] using
          (rcheck.frame_arr "trialActive" (by decide)).trans hactive
    · exact rbody.frame_arr "ord" (by decide) |>.trans hord
    · exact rbody.frame_arr "off" (by decide) |>.trans hoff
    · exact rbody.frame_arr "tgt" (by decide) |>.trans htarget
    · by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T
      · simpa [σ₄, σ₃, heq, σ₁] using hdomain₂
      · simpa [σ₄, σ₃, heq, σ₁] using hdomain₂
    · by_cases heq : activeTargets (target x) active
          (offset x v) (offset x (v + 1)) = T
      · simpa [σ₄, σ₃, heq, σ₁] using hmodulus₂
      · simpa [σ₄, σ₃, heq, σ₁] using hmodulus₂

end Lax457868Proofs.RepairClassScan
