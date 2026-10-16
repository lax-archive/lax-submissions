import Mathlib.Tactic
import Lax457868Proofs.RepairClassOffsets
import Lax457868Proofs.RepairTrialCheck
import Lax457868Proofs.RepairDomainSource
import Lax457868Proofs.ClassBucketDomain
import Lax457868Proofs.SamplerPhases
import Lax457868Proofs.SamplerLocalProbability
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
open Lax457868Proofs.SamplerLocalProbability
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ClassRepresentativeLoop

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

/-- The loop potential is exactly the sum of degree-local slot charges over
the remaining actual `ord` slice. -/
lemma repairClassPotential_eq_sum_Ico (stop cursor : ℕ)
    (weight : ℕ → ℕ) :
    repairClassPotential stop cursor weight =
      ∑ i ∈ Finset.Ico cursor stop, weight i := by
  generalize hm : stop - cursor = m
  induction m using Nat.strong_induction_on generalizing cursor with
  | h m ih =>
    by_cases hlt : cursor < stop
    · rw [repairClassPotential_step hlt,
        Finset.sum_eq_sum_Ico_succ_bot hlt]
      congr 1
      apply ih (stop - (cursor + 1))
      · omega
      · rfl
    · rw [repairClassPotential.eq_1]
      simp [hlt, Finset.Ico_eq_empty_of_le (by omega : stop ≤ cursor)]

/-- The source loop cost uses one charge per class slot and one charge per
actual CSR adjacency entry of that slot. -/
lemma repairClassPotential_eq_degree_sum (x : List ℕ) (ord : ℕ → ℕ)
    (start stop : ℕ) :
    repairClassPotential stop start (repairClassSlotWeight x ord) =
      90 * (∑ i ∈ Finset.Ico start stop,
        (offset x (ord i + 1) - offset x (ord i))) +
      70 * (stop - start) := by
  rw [repairClassPotential_eq_sum_Ico]
  simp only [repairClassSlotWeight, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp [Nat.card_Ico, Nat.mul_comm]

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

/-- All visited slots other than the distinguished vertex have a different
trace from the once-collected desired trace. -/
def scanSeparated (x : List ℕ) (active ord : ℕ → ℕ)
    (b : ℕ) (T : Finset ℕ) (start cursor : ℕ) : Prop :=
  ∀ j, start ≤ j → j < cursor → ord j ≠ b →
    activeTargets (target x) active (offset x (ord j))
      (offset x (ord j + 1)) ≠ T

private lemma scanSeparated_step {x : List ℕ} {active ord : ℕ → ℕ}
    {b start i : ℕ} {T : Finset ℕ} (hstart : start ≤ i) :
    scanSeparated x active ord b T start (i + 1) ↔
      scanSeparated x active ord b T start i ∧
        (ord i ≠ b → activeTargets (target x) active
          (offset x (ord i)) (offset x (ord i + 1)) ≠ T) := by
  constructor
  · intro h
    constructor
    · intro j hj hji hne
      exact h j hj (by omega) hne
    · exact h i hstart (by omega)
  · rintro ⟨hbefore, hlast⟩ j hj hji hne
    by_cases h : j < i
    · exact hbefore j hj h hne
    · have : j = i := by omega
      subst j
      exact hlast hne

/-- Run the fixed source while loop on the actual grouped `ord` slice. The
potential charges each visited CSR row's actual degree and one constant per
slot. Both scratch arrays remain valid inputs for the next iteration. -/
lemma repairClassScanWhile_run
    {B n targetCap b start stop : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env} {active ord rowList desiredMarks diffBuffer : ℕ → ℕ}
    {T : Finset ℕ} {d success : ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hcursor : σ.vars "repairScanCursor" = start)
    (hstart : σ.vars "repairStart" = start)
    (hstop : σ.vars "repairStop" = stop)
    (hrepairB : σ.vars "repairB" = b)
    (hsuccess : σ.vars "repairScanSuccess" = success)
    (hsuccess01 : success ≤ 1)
    (hsuccessGood : success = 1 ↔ scanSeparated x active ord b T start start)
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
    (hTrange : T ⊆ Finset.range n) (hd : d = T.card)
    (hstartStop : start ≤ stop) (hstopN : stop ≤ n)
    (hordRange : ∀ j, start ≤ j → j < stop → ord j < n)
    (hb : b < n) (hactiveB : ∀ w < n, active w < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' rowList' diffBuffer',
      Run B (.while (.lt (.var "repairScanCursor") (.var "repairStop"))
        repairClassScanBody) σ σ'
        (repairClassPotential stop start (repairClassSlotWeight x ord) + 4) ∧
      σ'.vars "repairScanCursor" = stop ∧
      (σ'.vars "repairScanSuccess" = 1 ↔
        scanSeparated x active ord b T start stop) ∧
      σ'.vars "repairScanSuccess" ≤ 1 ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n desiredMarks ∧
      σ'.arrs "trialRowList" = arrOf n rowList' ∧
      σ'.arrs "trialDiffList" = arrOf n diffBuffer' ∧
      σ'.arrs "trialActive" = arrOf n active ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" ∧
      σ'.vars "repairB" = b ∧ σ'.vars "repairStart" = start ∧
      σ'.vars "repairStop" = stop ∧ σ'.vars "trialDesiredLen" = d := by
  let weight := repairClassSlotWeight x ord
  let I : Env → Prop := fun τ =>
    start ≤ τ.vars "repairScanCursor" ∧
    τ.vars "repairScanCursor" ≤ stop ∧
    τ.vars "repairScanSuccess" ≤ 1 ∧
    (τ.vars "repairScanSuccess" = 1 ↔
      scanSeparated x active ord b T start (τ.vars "repairScanCursor")) ∧
    τ.vars "repairB" = b ∧ τ.vars "repairStart" = start ∧
    τ.vars "repairStop" = stop ∧ τ.vars "trialDesiredLen" = d ∧
    τ.vars "n" = n ∧
    τ.arrs "ord" = arrOf n ord ∧
    τ.arrs "off" = arrOf (n + 1) (offset x) ∧
    τ.arrs "tgt" = arrOf targetCap (target x) ∧
    τ.arrs "trialActive" = arrOf n active ∧
    τ.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
    τ.arrs "trialDesiredMarks" = arrOf n desiredMarks ∧
    (∃ rowList', τ.arrs "trialRowList" = arrOf n rowList') ∧
    (∃ diffBuffer', τ.arrs "trialDiffList" = arrOf n diffBuffer') ∧
    τ.arrs "drawDomain" = σ.arrs "drawDomain" ∧
    τ.vars "drawModulus" = σ.vars "drawModulus"
  let Φ : Env → ℕ := fun τ =>
    repairClassPotential stop (τ.vars "repairScanCursor") weight
  have hI : I σ := by
    dsimp [I]
    refine ⟨by omega, by omega, by simpa [hsuccess] using hsuccess01,
      ?_, hrepairB, hstart, hstop, hdesiredLen, hn, hord, hoff,
      htarget, hactive, hrowMarks, hdesiredMarks,
      ⟨rowList, hrowList⟩, ⟨diffBuffer, hdiffList⟩, rfl, rfl⟩
    simpa [hcursor, hsuccess] using hsuccessGood
  have hdef : ∀ τ, I τ →
      ∃ v, (Cond.lt (.var "repairScanCursor") (.var "repairStop")).evalB B τ = some v := by
    intro τ hτ
    rcases hτ with ⟨_, hle, _, _, _, _, hstopτ, _, _, -⟩
    exact evalB_condLt_vars
      (by omega)
      (by rw [hstopτ]; omega)
  have hstep : ∀ τ, I τ →
      (Cond.lt (.var "repairScanCursor") (.var "repairStop")).evalB B τ = some true →
      ∃ τ' K, Run B repairClassScanBody τ τ' K ∧ I τ' ∧
        1 + (Cond.lt (.var "repairScanCursor") (.var "repairStop")).size +
          K + Φ τ' ≤ Φ τ := by
    intro τ hτ hcond
    rcases hτ with ⟨hstartτ, hleτ, hsuccess01τ, hgoodτ,
      hbτ, hstartτ', hstopτ, hdτ, hnτ, hordτ, hoffτ, htgtτ,
      hactiveτ, hrowMarksτ, hdesiredMarksτ, ⟨rowListτ, hrowListτ⟩,
      ⟨diffBufferτ, hdiffBufferτ⟩, hdomainτ, hmodulusτ⟩
    let i := τ.vars "repairScanCursor"
    have hiStop : i < stop := by
      have h := lt_of_condLt_true hcond
      simpa [i, hstopτ] using h
    have hiN : i < n := lt_of_lt_of_le hiStop hstopN
    have hvN : ord i < n := hordRange i hstartτ hiStop
    obtain ⟨τ', rowList', diffBuffer', rbody, hs', hc', _, hrm', hdm',
      hrl', hdl', ha', ho', hf', ht', hdomain', hmodulus'⟩ :=
      repairClassScanBody_run (rowMarks := fun _ => 0)
        (success := τ.vars "repairScanSuccess")
        hx htargetCap (by rfl) hbτ
        rfl hnτ hordτ hoffτ htgtτ
        hactiveτ hrowMarksτ hrowListτ hdτ hdesiredMarksτ hdiffBufferτ
        hdesiredMarks01 hdesiredMarksMem hTrange hd hiN rfl hb hvN
        hactiveB hn1B htargetCapB hnB honeB
    have hcard : (activeTargets (target x) active
        (offset x (ord i)) (offset x (ord i + 1))).card ≤
        offset x (ord i + 1) - offset x (ord i) :=
      card_activeTargets_le_interval
    have hbudget : 54 * (offset x (ord i + 1) - offset x (ord i)) + 22 +
        36 * (activeTargets (target x) active (offset x (ord i))
          (offset x (ord i + 1))).card + 44 + 4 ≤ weight i := by
      dsimp [weight, repairClassSlotWeight]
      omega
    have hgood' : τ'.vars "repairScanSuccess" = 1 ↔
        scanSeparated x active ord b T start (i + 1) := by
      have hgoodi : τ.vars "repairScanSuccess" = 1 ↔
          scanSeparated x active ord b T start i := by
        simpa only [i] using hgoodτ
      rw [hs', scanSeparated_step hstartτ]
      change _ ↔ scanSeparated x active ord b T start i ∧
        (ord i ≠ b → activeTargets (target x) active
          (offset x (ord i)) (offset x (ord i + 1)) ≠ T)
      by_cases hbi : ord i = b
      · simpa [hbi] using hgoodi
      · by_cases heq : activeTargets (target x) active
            (offset x (ord i)) (offset x (ord i + 1)) = T
        · simp [hbi, heq]
        · simpa [hbi, heq] using hgoodi
    have hsuccess01' : τ'.vars "repairScanSuccess" ≤ 1 := by
      rw [hs']
      split_ifs <;> omega
    have hI' : I τ' := by
      dsimp [I]
      refine ⟨?_, ?_, hsuccess01', ?_, ?_, ?_, ?_, ?_, ?_, ho', hf', ht',
        ha', hrm', hdm', ⟨rowList', hrl'⟩, ⟨diffBuffer', hdl'⟩,
        hdomain'.trans hdomainτ, hmodulus'.trans hmodulusτ⟩
      · rw [hc']; omega
      · rw [hc']; omega
      · simpa [hc'] using hgood'
      · exact rbody.frame_var "repairB" (by decide) |>.trans hbτ
      · exact rbody.frame_var "repairStart" (by decide) |>.trans hstartτ'
      · exact rbody.frame_var "repairStop" (by decide) |>.trans hstopτ
      · exact rbody.frame_var "trialDesiredLen" (by decide) |>.trans hdτ
      · exact rbody.frame_var "n" (by decide) |>.trans hnτ
    refine ⟨τ', _, rbody, hI', ?_⟩
    dsimp [Φ]
    rw [hc', show τ.vars "repairScanCursor" = i from rfl,
      repairClassPotential_step hiStop]
    dsimp [weight, repairClassSlotWeight] at hbudget ⊢
    norm_num [Cond.size, Expr.size] at hbudget ⊢
    omega
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential I Φ hdef hstep hI
  rcases hI' with ⟨_, hle', hs01', hgood', hb', hstart', hstop', hd',
    _, hord', hoff', htgt', hactive', hrm', hdm', ⟨rowList', hrl'⟩,
    ⟨diffBuffer', hdl'⟩, hdomain', hmodulus'⟩
  have hcursor' : σ'.vars "repairScanCursor" = stop := by
    have hge := le_of_condLt_false hfalse
    omega
  have hpay' : K ≤ repairClassPotential stop start weight + 4 := by
    dsimp [Φ] at hpay
    rw [hcursor, hcursor'] at hpay
    have hz : repairClassPotential stop stop weight = 0 := by
      rw [repairClassPotential.eq_1]
      simp
    rw [hz] at hpay
    omega
  refine ⟨σ', rowList', diffBuffer', hrun.mono hpay', hcursor', ?_,
    hs01', hrm', hdm', hrl', hdl', hactive', hord', hoff', htgt',
    hdomain', hmodulus', hb', hstart', hstop', hd'⟩
  simpa [hcursor'] using hgood'

/-- The initialized source loop uses the same fixed interval and success
meaning as its checked while command. -/
lemma repairClassScanLoop_run
    {B n targetCap b start stop : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env} {active ord rowList desiredMarks diffBuffer : ℕ → ℕ}
    {T : Finset ℕ} {d : ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hstart : σ.vars "repairStart" = start)
    (hstop : σ.vars "repairStop" = stop)
    (hrepairB : σ.vars "repairB" = b)
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
    (hTrange : T ⊆ Finset.range n) (hd : d = T.card)
    (hstartStop : start ≤ stop) (hstopN : stop ≤ n)
    (hordRange : ∀ j, start ≤ j → j < stop → ord j < n)
    (hb : b < n) (hactiveB : ∀ w < n, active w < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' rowList' diffBuffer',
      Run B repairClassScanLoop σ σ'
        (repairClassPotential stop start (repairClassSlotWeight x ord) + 8) ∧
      σ'.vars "repairScanCursor" = stop ∧
      (σ'.vars "repairScanSuccess" = 1 ↔
        scanSeparated x active ord b T start stop) ∧
      σ'.vars "repairScanSuccess" ≤ 1 ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n desiredMarks ∧
      σ'.arrs "trialRowList" = arrOf n rowList' ∧
      σ'.arrs "trialDiffList" = arrOf n diffBuffer' ∧
      σ'.arrs "trialActive" = arrOf n active ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" ∧
      σ'.vars "repairB" = b ∧ σ'.vars "repairStart" = start ∧
      σ'.vars "repairStop" = stop ∧ σ'.vars "trialDesiredLen" = d := by
  let σ₁ := σ.setVar "repairScanSuccess" 1
  let σ₂ := σ₁.setVar "repairScanCursor" start
  have rfirst : Run B (.assign "repairScanSuccess" (.lit 1)) σ σ₁ 2 := by
    simpa [σ₁] using Run.assign (evalB_lit honeB)
  have rsecond : Run B (.assign "repairScanCursor" (.var "repairStart")) σ₁ σ₂ 2 := by
    have heval : (Expr.var "repairStart").evalB B σ₁ = some start := by
      rw [evalB_var_iff]
      exact ⟨by simp [σ₁, hstart], by simp [σ₁, hstart]; omega⟩
    simpa [σ₂] using Run.assign heval
  have hinitGood : (σ₂.vars "repairScanSuccess" = 1 ↔
      scanSeparated x active ord b T start start) := by
    constructor
    · intro _ j hj hj'
      omega
    · intro _
      simp [σ₂, σ₁]
  obtain ⟨σ', rowList', diffBuffer', rwhile, hc, hs, hs01, hrm, hdm,
    hrl, hdl, ha, ho, hf, ht, hdomain, hmodulus, hb', hstart', hstop', hd'⟩ :=
    repairClassScanWhile_run (σ := σ₂) (success := 1)
      hx htargetCap
      (by simp [σ₂]) (by simpa [σ₂, σ₁] using hstart)
      (by simpa [σ₂, σ₁] using hstop)
      (by simpa [σ₂, σ₁] using hrepairB)
      (by simp [σ₂, σ₁]) (by omega) hinitGood
      (by simpa [σ₂, σ₁] using hn)
      (by simpa [σ₂, σ₁] using hord)
      (by simpa [σ₂, σ₁] using hoff)
      (by simpa [σ₂, σ₁] using htarget)
      (by simpa [σ₂, σ₁] using hactive)
      (by simpa [σ₂, σ₁] using hrowMarks)
      (by simpa [σ₂, σ₁] using hrowList)
      (by simpa [σ₂, σ₁] using hdesiredLen)
      (by simpa [σ₂, σ₁] using hdesiredMarks)
      (by simpa [σ₂, σ₁] using hdiffList)
      hdesiredMarks01 hdesiredMarksMem hTrange hd hstartStop hstopN
      hordRange hb hactiveB hn1B htargetCapB hnB honeB
  refine ⟨σ', rowList', diffBuffer', ?_, hc, hs, hs01, hrm, hdm,
    hrl, hdl, ha, ho, hf, ht, ?_, ?_, hb', hstart', hstop', hd'⟩
  · have h := rfirst.seq (rsecond.seq rwhile)
    have hcost : 2 + (2 +
        (repairClassPotential stop start (repairClassSlotWeight x ord) + 4)) =
        repairClassPotential stop start (repairClassSlotWeight x ord) + 8 := by
      omega
    simpa only [repairClassScanLoop, seqs, hcost] using h
  · simpa [σ₂, σ₁] using hdomain
  · simpa [σ₂, σ₁] using hmodulus

/-- Collect the desired trace once, execute the class loop, and clear exactly
the desired entries collected. The cost charges the distinguished CSR row
once and every actual class-slice CSR row once. -/
lemma repairClassScanSource_run
    {B n targetCap b start stop : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env} {active ord rowList desiredList diffBuffer : ℕ → ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hstart : σ.vars "repairStart" = start)
    (hstop : σ.vars "repairStop" = stop)
    (hrepairB : σ.vars "repairB" = b)
    (hn : σ.vars "n" = n)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs "trialActive" = arrOf n active)
    (hrowMarks : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hrowList : σ.arrs "trialRowList" = arrOf n rowList)
    (hdesiredMarks : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0))
    (hdesiredList : σ.arrs "trialDesiredList" = arrOf n desiredList)
    (hdiffList : σ.arrs "trialDiffList" = arrOf n diffBuffer)
    (hstartStop : start ≤ stop) (hstopN : stop ≤ n)
    (hordRange : ∀ j, start ≤ j → j < stop → ord j < n)
    (hb : b < n) (hactiveB : ∀ w < n, active w < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B repairClassScanSource σ σ'
        (54 * (offset x (b + 1) - offset x b) +
          12 * (activeTargets (target x) active
            (offset x b) (offset x (b + 1))).card +
          repairClassPotential stop start (repairClassSlotWeight x ord) + 36) ∧
      (σ'.vars "repairScanSuccess" = 1 ↔
        scanSeparated x active ord b
          (activeTargets (target x) active
            (offset x b) (offset x (b + 1))) start stop) ∧
      σ'.vars "repairScanSuccess" ≤ 1 ∧
      σ'.vars "repairScanCursor" = stop ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialActive" = arrOf n active ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" := by
  let T := activeTargets (target x) active (offset x b) (offset x (b + 1))
  have htargetRange : ∀ j, offset x b ≤ j → j < offset x (b + 1) →
      target x j < n := by
    intro j _ hj
    apply hx.target_lt j
    rw [← htargetCap]
    exact hj.trans_le (by
      rw [htargetCap, ← hx.offset_last]
      exact offset_mono' hx (by omega) le_rfl)
  have hTrange : T ⊆ Finset.range n := activeTargets_subset_range htargetRange
  obtain ⟨σ₁, desiredMarks, desiredList', rcollect, hmarks₁, hlist₁,
    hlen₁, henum₁, hmem₁, h01₁, hactive₁, htgt₁, hoff₁,
    hdomain₁, hmodulus₁, _, _⟩ :=
    collectDesiredTrace_run (desiredMarks := fun _ => 0)
      hx htargetCap hrepairB hn hoff htarget
      hactive hdesiredMarks hdesiredList hb hactiveB hn1B htargetCapB
  have hstart₁ : σ₁.vars "repairStart" = start :=
    (rcollect.frame_var "repairStart" (by decide)).trans hstart
  have hstop₁ : σ₁.vars "repairStop" = stop :=
    (rcollect.frame_var "repairStop" (by decide)).trans hstop
  have hb₁ : σ₁.vars "repairB" = b :=
    (rcollect.frame_var "repairB" (by decide)).trans hrepairB
  have hn₁ : σ₁.vars "n" = n :=
    (rcollect.frame_var "n" (by decide)).trans hn
  have hord₁ : σ₁.arrs "ord" = arrOf n ord :=
    (rcollect.frame_arr "ord" (by decide)).trans hord
  have hrowMarks₁ : σ₁.arrs "trialRowMarks" = arrOf n (fun _ => 0) :=
    (rcollect.frame_arr "trialRowMarks" (by decide)).trans hrowMarks
  have hrowList₁ : σ₁.arrs "trialRowList" = arrOf n rowList :=
    (rcollect.frame_arr "trialRowList" (by decide)).trans hrowList
  have hdiffList₁ : σ₁.arrs "trialDiffList" = arrOf n diffBuffer :=
    (rcollect.frame_arr "trialDiffList" (by decide)).trans hdiffList
  obtain ⟨σ₂, _, _, rloop, hc₂, hsuccess₂, hsuccess01₂,
    hrowMarks₂, _hdesiredMarks₂, _, _, hactive₂, hord₂,
    _, _, _, _, _, _, _, hlen₂⟩ :=
    repairClassScanLoop_run hx htargetCap hstart₁ hstop₁ hb₁ hn₁
      hord₁ (hoff₁.trans hoff) htgt₁ (hactive₁.trans hactive)
      hrowMarks₁ hrowList₁ hlen₁ hmarks₁ hdiffList₁
      h01₁ hmem₁ hTrange rfl hstartStop hstopN hordRange hb
      hactiveB hn1B htargetCapB hnB honeB
  have hlen₂' : σ₂.vars "trialDesiredLen" = T.card := by
    simpa [T] using hlen₂
  have hn₂ : σ₂.vars "n" = n :=
    (rloop.frame_var "n" (by decide)).trans hn₁
  have hlist₂ : σ₂.arrs "trialDesiredList" = arrOf n desiredList' :=
    (rloop.frame_arr "trialDesiredList" (by decide)).trans hlist₁
  have hmarks₂ : σ₂.arrs "trialDesiredMarks" = arrOf n desiredMarks :=
    (rloop.frame_arr "trialDesiredMarks" (by decide)).trans hmarks₁
  obtain ⟨σ₃, rclear, hmarks₃, _, _, _⟩ :=
    clearDesiredTrace_run hn₂ hlen₂' hmarks₂ hlist₂ henum₁
      hTrange h01₁ hmem₁ hnB
  have rsource : Run B repairClassScanSource σ σ₃
      (54 * (offset x (b + 1) - offset x b) + 12 * T.card +
        repairClassPotential stop start (repairClassSlotWeight x ord) + 36) := by
    have h := rcollect.seq (rloop.seq rclear)
    have hcost : (54 * (offset x (b + 1) - offset x b) + 22) +
      ((repairClassPotential stop start (repairClassSlotWeight x ord) + 8) +
        (12 * T.card + 6)) =
      54 * (offset x (b + 1) - offset x b) + 12 * T.card +
        repairClassPotential stop start (repairClassSlotWeight x ord) + 36 := by
      omega
    simpa only [repairClassScanSource, seqs, hcost] using h
  refine ⟨σ₃, by simpa [T] using rsource, ?_, ?_, ?_, ?_,
    hmarks₃, ?_, ?_, ?_, ?_⟩
  · rw [rclear.frame_var "repairScanSuccess" (by decide)]
    exact hsuccess₂
  · rw [rclear.frame_var "repairScanSuccess" (by decide)]
    exact hsuccess01₂
  · exact (rclear.frame_var "repairScanCursor" (by decide)).trans hc₂
  · exact (rclear.frame_arr "trialRowMarks" (by decide)).trans hrowMarks₂
  · exact (rclear.frame_arr "trialActive" (by decide)).trans hactive₂
  · exact (rclear.frame_arr "ord" (by decide)).trans hord₂
  · exact rsource.frame_arr "drawDomain" (by decide)
  · exact rsource.frame_var "drawModulus" (by decide)

/-- Membership in a materialized class slice is precisely membership among
the positions visited by the source loop. -/
private lemma mem_classSlice_iff {start stop : ℕ} {ord : ℕ → ℕ}
    {C : Finset ℕ} (hstartStop : start ≤ stop)
    (henum : PrefixEnumerates (stop - start)
      (fun i => ord (start + i)) C) (v : ℕ) :
    v ∈ C ↔ ∃ j, start ≤ j ∧ j < stop ∧ ord j = v := by
  rw [← henum.2]
  simp only [Stack.toList, arrOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨start + i, by omega, by omega, rfl⟩
  · rintro ⟨j, hj, hjstop, rfl⟩
    refine ⟨j - start, by omega, ?_⟩
    congr 1
    omega

private lemma scanSeparated_iff_class
    {x : List ℕ} {active ord : ℕ → ℕ} {b start stop : ℕ}
    {T C : Finset ℕ} (hstartStop : start ≤ stop)
    (henum : PrefixEnumerates (stop - start)
      (fun i => ord (start + i)) C) :
    scanSeparated x active ord b T start stop ↔
      ∀ v ∈ C, v ≠ b →
        activeTargets (target x) active (offset x v) (offset x (v + 1)) ≠ T := by
  constructor
  · intro h v hv hvb
    obtain ⟨j, hj, hjstop, rfl⟩ :=
      (mem_classSlice_iff hstartStop henum v).mp hv
    exact h j hj hjstop hvb
  · intro h j hj hjstop hvb
    exact h (ord j)
      ((mem_classSlice_iff hstartStop henum (ord j)).mpr
        ⟨j, hj, hjstop, rfl⟩) hvb

/-- The complete fixed lookup-and-scan source reads class bounds from the
runtime arrays, then scans exactly the corresponding grouped slice. The
grouped-B mask used to size `xs` is independent of the trial sample flags. -/
lemma repairClassLookupAndScan_run
    {B n q targetCap b : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env}
    {size starts label ord groupActive active rowList desiredList diffBuffer : ℕ → ℕ}
    {xs : List ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hn : σ.vars "n" = n)
    (hq : σ.vars "classCount" = q)
    (hrep : σ.vars "repairB" = b)
    (hclassB : σ.arrs "classB" = arrOf n label)
    (hsizes : σ.arrs "classSize" = arrOf n size)
    (hstarts : σ.arrs "repairClassStart" = arrOf n starts)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs "trialActive" = arrOf n active)
    (hrowMarks : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hrowList : σ.arrs "trialRowList" = arrOf n rowList)
    (hdesiredMarks : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0))
    (hdesiredList : σ.arrs "trialDesiredList" = arrOf n desiredList)
    (hdiffList : σ.arrs "trialDiffList" = arrOf n diffBuffer)
    (hb : b < n) (hqle : q ≤ n) (hlabel : label b < q)
    (hstartTable : ∀ d < q, starts d = classStart size d)
    (hclassEnd : ∀ d < q, classStart size d + size d ≤ xs.length)
    (hxsCard : xs.length = (activeVertices n groupActive).card)
    (hxsRange : xs.toFinset ⊆ Finset.range n)
    (hactiveCard : (activeVertices n groupActive).card ≤ n)
    (hslices : ∀ d < q, PrefixEnumerates (size d)
      (fun i => ord (classStart size d + i))
      (labelClass xs label d))
    (hactiveB : ∀ w < n, active w < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B repairClassLookupAndScan σ σ'
        (54 * (offset x (b + 1) - offset x b) +
          12 * (activeTargets (target x) active
            (offset x b) (offset x (b + 1))).card +
          repairClassPotential
            (classStart size (label b) + size (label b))
            (classStart size (label b))
            (repairClassSlotWeight x ord) + 47) ∧
      (σ'.vars "repairScanSuccess" = 1 ↔
        ∀ v ∈ labelClass xs label (label b), v ≠ b →
          activeTargets (target x) active (offset x v)
            (offset x (v + 1)) ≠
          activeTargets (target x) active (offset x b)
            (offset x (b + 1))) ∧
      σ'.vars "repairScanSuccess" ≤ 1 ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" ∧
      σ'.arrs "repB" = σ.arrs "repB" ∧
      σ'.arrs "classB" = σ.arrs "classB" ∧
      σ'.arrs "classSize" = σ.arrs "classSize" ∧
      σ'.arrs "sampleFlags" = σ.arrs "sampleFlags" := by
  let d := label b
  let start := classStart size d
  let stop := start + size d
  obtain ⟨σ₁, rlookup, _, hstart₁, hstop₁, _, _, _, hslice,
    _, _, _, hordFrame, hord₁, _, _, hvars, hn₁, _, _, _⟩ :=
    repairClassLookup_run hn hq hrep hclassB hsizes hstarts hord hb
      hqle hlabel hstartTable hclassEnd hxsCard hactiveCard hslices hnB
  have hstartStop : start ≤ stop := by dsimp [stop]; omega
  have hstopN : stop ≤ n := by
    dsimp [stop, start, d]
    exact (hclassEnd (label b) hlabel).trans
      (hxsCard.trans_le hactiveCard)
  have hClassRange : ∀ v ∈ labelClass xs label d, v < n := by
    intro v hv
    apply Finset.mem_range.mp
    apply hxsRange
    exact (Finset.mem_filter.mp hv).1
  have hslice' : PrefixEnumerates (stop - start)
      (fun i => ord (start + i)) (labelClass xs label d) := by
    simpa [hstart₁, hstop₁, start, stop, d] using hslice
  have hordRange : ∀ j, start ≤ j → j < stop → ord j < n := by
    intro j hj hjstop
    have hi : j - start < stop - start := by omega
    have hentry := PrefixEnumerates.entry_lt hslice' hClassRange
      (j - start) hi
    simpa [start, Nat.add_sub_of_le hj] using hentry
  have hsourceInput : σ₁.vars "repairB" = b :=
    hvars "repairB" (by decide) (by decide) (by decide) |>.trans hrep
  obtain ⟨σ₂, rsource, hsuccess, hsuccess01, _, hrowMarks₂,
    hdesiredMarks₂, _, _, _, _⟩ :=
    repairClassScanSource_run hx htargetCap
      hstart₁ hstop₁ hsourceInput hn₁ hord₁
      ((rlookup.frame_arr "off" (by decide)).trans hoff)
      ((rlookup.frame_arr "tgt" (by decide)).trans htarget)
      ((rlookup.frame_arr "trialActive" (by decide)).trans hactive)
      ((rlookup.frame_arr "trialRowMarks" (by decide)).trans hrowMarks)
      ((rlookup.frame_arr "trialRowList" (by decide)).trans hrowList)
      ((rlookup.frame_arr "trialDesiredMarks" (by decide)).trans hdesiredMarks)
      ((rlookup.frame_arr "trialDesiredList" (by decide)).trans hdesiredList)
      ((rlookup.frame_arr "trialDiffList" (by decide)).trans hdiffList)
      hstartStop hstopN hordRange hb hactiveB hn1B htargetCapB hnB honeB
  have rfull : Run B repairClassLookupAndScan σ σ₂
      (54 * (offset x (b + 1) - offset x b) +
        12 * (activeTargets (target x) active
          (offset x b) (offset x (b + 1))).card +
        repairClassPotential stop start (repairClassSlotWeight x ord) + 47) := by
    have h := rlookup.seq rsource
    have hcost : 11 + (54 * (offset x (b + 1) - offset x b) +
        12 * (activeTargets (target x) active
          (offset x b) (offset x (b + 1))).card +
        repairClassPotential stop start (repairClassSlotWeight x ord) + 36) =
        54 * (offset x (b + 1) - offset x b) +
          12 * (activeTargets (target x) active
            (offset x b) (offset x (b + 1))).card +
          repairClassPotential stop start (repairClassSlotWeight x ord) + 47 := by
      omega
    have h' : Run B (repairClassLookup.seq repairClassScanSource) σ σ₂
        (54 * (offset x (b + 1) - offset x b) +
          12 * (activeTargets (target x) active
            (offset x b) (offset x (b + 1))).card +
          repairClassPotential stop start (repairClassSlotWeight x ord) + 47) := by
      convert h using 1 <;> dsimp [start, stop, d] <;> omega
    simpa only [repairClassLookupAndScan, seqs] using h'
  refine ⟨σ₂, by simpa [start, stop, d] using rfull, ?_,
    hsuccess01, hrowMarks₂, hdesiredMarks₂,
    rfull.frame_arr "drawDomain" (by decide),
    rfull.frame_var "drawModulus" (by decide),
    rfull.frame_arr "repB" (by decide),
    rfull.frame_arr "classB" (by decide),
    rfull.frame_arr "classSize" (by decide),
    rfull.frame_arr "sampleFlags" (by decide)⟩
  rw [scanSeparated_iff_class hstartStop hslice'] at hsuccess
  simpa [start, stop, d] using hsuccess

/-- Translate the CSR predicate exported by the checked runtime source into
the graph's trace predicate for a fixed sample. -/
lemma classScanCondition_iff_graphTrace
    {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (W C : Finset ℕ)
    (hW : W ⊆ Finset.range n) (hC : C ⊆ Finset.range n)
    {b : ℕ} (hb : b < n) :
    (∀ v ∈ C, v ≠ b →
      activeTargets (target x) (setFlag W) (offset x v)
        (offset x (v + 1)) ≠
      activeTargets (target x) (setFlag W) (offset x b)
        (offset x (b + 1))) ↔
    (∀ v ∈ C, v ≠ b →
      trace (numericNeighborhood G) W v ≠
        trace (numericNeighborhood G) W b) := by
  have hbTrace := desiredTrace_eq_numericTrace hx W hW hb
  constructor
  · intro h v hv hvb
    have hvn : v < n := Finset.mem_range.mp (hC hv)
    rw [← desiredTrace_eq_numericTrace hx W hW hvn, ← hbTrace]
    exact h v hv hvb
  · intro h v hv hvb
    have hvn : v < n := Finset.mem_range.mp (hC hv)
    rw [desiredTrace_eq_numericTrace hx W hW hvn, hbTrace]
    exact h v hv hvb

/-- When the supplied fixed class is the old phase-two trace fibre, the
success condition is precisely the existing local-trial isolation event.
This bridge does not recompute the class after a proposed repair. -/
lemma classGraphTrace_iff_localTrialIsolates
    {n : ℕ} (G : SimpleGraph (Fin n))
    (B W C : Finset ℕ) (b : ℕ) (draws : List ℕ)
    (hC : C = B.filter (fun v =>
      trace (numericNeighborhood G) W b =
        trace (numericNeighborhood G) W v)) :
    (∀ v ∈ C, v ≠ b →
      trace (numericNeighborhood G) (W ∪ draws.toFinset) v ≠
        trace (numericNeighborhood G) (W ∪ draws.toFinset) b) ↔
      localTrialIsolates (numericNeighborhood G) B W b draws := by
  simp only [localTrialIsolates]
  constructor
  · intro h v hv htrace hvb
    exact (h v (by simpa [hC, hv, htrace] using
      (show v ∈ B.filter (fun v =>
        trace (numericNeighborhood G) W b =
          trace (numericNeighborhood G) W v) from
        Finset.mem_filter.mpr ⟨hv, htrace⟩)) hvb).symm
  · intro h v hv hvb
    have hvc : v ∈ B ∧ trace (numericNeighborhood G) W b =
        trace (numericNeighborhood G) W v := by
      simpa [hC] using hv
    exact (h v hvc.1 hvc.2 hvb).symm

/-- On the fixed old trace fibre, testing only the new draws gives the same
isolation answer as testing the enlarged sample. Both sides are the same
distinguishing-draw event, including when a draw also lies in the old sample. -/
lemma classDrawTrace_iff_localTrialIsolates
    {n : ℕ} (G : SimpleGraph (Fin n))
    (B W C : Finset ℕ) (b : ℕ) (draws : List ℕ)
    (hC : C = B.filter (fun v =>
      trace (numericNeighborhood G) W b =
        trace (numericNeighborhood G) W v)) :
    (∀ v ∈ C, v ≠ b →
      trace (numericNeighborhood G) draws.toFinset v ≠
        trace (numericNeighborhood G) draws.toFinset b) ↔
      localTrialIsolates (numericNeighborhood G) B W b draws := by
  constructor
  · intro h v hv hbase hvb
    have hvC : v ∈ C := by
      rw [hC]
      exact Finset.mem_filter.mpr ⟨hv, hbase⟩
    have hdraws : ∃ a ∈ draws,
        a ∈ distinguishingRange (numericNeighborhood G) b v := by
      exact (trace_ne_iff_draw_hits (numericNeighborhood G) ∅ b v draws
        (by simp [trace])).mp (by simpa using (h v hvC hvb).symm)
    exact (trace_ne_iff_draw_hits (numericNeighborhood G) W b v draws hbase).mpr
      hdraws
  · intro h v hvC hvb
    have hv' : v ∈ B.filter (fun w =>
        trace (numericNeighborhood G) W b =
          trace (numericNeighborhood G) W w) := by
      simpa [hC] using hvC
    have hvB := (Finset.mem_filter.mp hv').1
    have hbase := (Finset.mem_filter.mp hv').2
    have hdraws : ∃ a ∈ draws,
        a ∈ distinguishingRange (numericNeighborhood G) b v :=
      (trace_ne_iff_draw_hits (numericNeighborhood G) W b v draws hbase).mp
        (h v hvB hbase hvb)
    have hsep :=
      (trace_ne_iff_draw_hits (numericNeighborhood G) ∅ b v draws
        (by simp [trace])).mpr hdraws
    exact (by simpa using hsep.symm)

/-- A checked scan result can be read as the existing local-trial event when
the caller supplies the fixed old trace class and the trial's sample flags. -/
lemma scanSuccess_iff_localTrialIsolates
    {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G)
    (B W C : Finset ℕ) (b : ℕ) (draws : List ℕ)
    (hSrange : draws.toFinset ⊆ Finset.range n)
    (hCrange : C ⊆ Finset.range n) (hb : b < n)
    (hC : C = B.filter (fun v =>
      trace (numericNeighborhood G) W b =
        trace (numericNeighborhood G) W v))
    {active : ℕ → ℕ} {σ' : Env}
    (hactive : active = setFlag draws.toFinset)
    (hsuccess : σ'.vars "repairScanSuccess" = 1 ↔
      ∀ v ∈ C, v ≠ b →
        activeTargets (target x) active (offset x v)
          (offset x (v + 1)) ≠
        activeTargets (target x) active (offset x b)
          (offset x (b + 1))) :
    σ'.vars "repairScanSuccess" = 1 ↔
      localTrialIsolates (numericNeighborhood G) B W b draws := by
  rw [hsuccess]
  simpa [hactive] using
    (classScanCondition_iff_graphTrace hx draws.toFinset C
      hSrange hCrange hb).trans
      (classDrawTrace_iff_localTrialIsolates G B W C b draws hC)

/-- For members of the fixed old trace class, the graph event above is
equivalent to every other member being hit by a distinguishing draw. -/
lemma classGraphTrace_iff_drawHits
    {n : ℕ} (G : SimpleGraph (Fin n))
    (B W C : Finset ℕ) (b : ℕ) (draws : List ℕ)
    (hC : C = B.filter (fun v =>
      trace (numericNeighborhood G) W b =
        trace (numericNeighborhood G) W v)) :
    (∀ v ∈ C, v ≠ b →
      trace (numericNeighborhood G) (W ∪ draws.toFinset) v ≠
        trace (numericNeighborhood G) (W ∪ draws.toFinset) b) ↔
    (∀ v ∈ C, v ≠ b →
      ∃ a ∈ draws,
        a ∈ distinguishingRange (numericNeighborhood G) b v) := by
  constructor
  · intro h v hv hvb
    have hv' : v ∈ B.filter (fun w =>
        trace (numericNeighborhood G) W b =
          trace (numericNeighborhood G) W w) := by
      simpa [hC] using hv
    have hbase : trace (numericNeighborhood G) W b =
        trace (numericNeighborhood G) W v :=
      (Finset.mem_filter.mp hv').2
    exact (trace_ne_iff_draw_hits (numericNeighborhood G) W b v draws hbase).mp
      (h v hv hvb).symm
  · intro h v hv hvb
    have hv' : v ∈ B.filter (fun w =>
        trace (numericNeighborhood G) W b =
          trace (numericNeighborhood G) W w) := by
      simpa [hC] using hv
    have hbase : trace (numericNeighborhood G) W b =
        trace (numericNeighborhood G) W v :=
      (Finset.mem_filter.mp hv').2
    exact ((trace_ne_iff_draw_hits (numericNeighborhood G) W b v draws hbase).mpr
      (h v hv hvb)).symm

end Lax457868Proofs.RepairClassScan
