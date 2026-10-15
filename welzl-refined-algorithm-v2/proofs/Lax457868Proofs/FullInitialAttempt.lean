import Lax457868Proofs.InitialSamplerChoice
import Lax457868Proofs.InitialAttemptAcceptance
import Lax457868Proofs.ReusedOriginal.Construction.RadixEight

/-! One fixed initial attempt, including the actual exception computation and
acceptance decision. The two capped failure branches leave the initial
zero acceptance bit in place. -/

namespace Lax457868Proofs.FullInitialAttempt

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.InitialSamplerChoice
open Lax457868Proofs.InitialAttemptAcceptance
open Lax457868Proofs.InitialDrawSampleSource
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.SequentialDraws
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ExceptionCollection
open Lax457868Proofs.ReusedOriginal.Construction.NearSweepMath

noncomputable section

/-- All three runtime paths belong to one fixed source. -/
def fullInitialAttempt : Com :=
  initialSamplerAttempt.seq
    (.ite (.eq (.var "batchFailed") (.lit 0))
      (.ite (.eq (.var "repFailed") (.lit 0))
        initialAttemptAcceptance .skip)
      .skip)

lemma bounded_active_flags_eq_setFlag {n : ℕ} {active : ℕ → ℕ}
    (h01 : ∀ v < n, active v ≤ 1) :
    arrOf n active = arrOf n (setFlag (activeVertices n active)) := by
  apply List.ext_getElem
  · simp [arrOf]
  · intro v hv hv'
    have hvn : v < n := by simpa [arrOf] using hv
    have hvalue : active v = setFlag (activeVertices n active) v := by
      by_cases hactive : active v = 1
      · simp [setFlag, mem_activeVertices, hvn, hactive]
      · have hz : active v = 0 := by have h := h01 v hvn; omega
        simp [setFlag, mem_activeVertices, hz]
    simp [arrOf, hvalue]

private lemma guard_eval {B : ℕ} {σ : Env} {v : String} {b : Bool}
    (h : σ.vars v = if b then 1 else 0) (hone : 1 < B) :
    (Cond.eq (.var v) (.lit 0)).evalB B σ = some (!b) := by
  have hvar : (Expr.var v).evalB B σ = some (if b then 1 else 0) := by
    rw [evalB_var_iff]
    refine ⟨h.symm, ?_⟩
    rw [h]
    cases b <;> norm_num <;> omega
  have hlit : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
  rw [evalB_condEq hvar hlit]
  cases b <;> rfl

lemma exception_flags_eq_setFlag {n u : ℕ} {x : List ℕ}
    {A C : Finset ℕ} {rep : ℕ → ℕ} :
    arrOf n
      (exceptionValue u (setFlag C) rep
        (degreePrefix (target x) (offset x) (setFlag A) (setFlag C) n)
        (commonPrefix (target x) (offset x) (setFlag A) (setFlag C) rep n)) =
    arrOf n (setFlag (attemptExceptions n u x A C rep)) := by
  apply List.ext_getElem
  · simp [arrOf]
  · intro b hb hb'
    have hbN : b < n := by simpa [arrOf] using hb
    simp [arrOf, exceptionValue, attemptExceptions, exceptionSet,
      setFlag, hbN]

/-- The checked execution of one whole attempt. Both capped selection failures
return with the initialized zero bit; the successful branch computes exactly
the exception set of the proof-side `InitialChoice`. The selection-state Run
and draw trace are retained for coupling to the randomized argument. -/
lemma fullInitialAttempt_run_bits
    {B n m domainCap r t bufferCap targetCap Q k cap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Input B n m domainCap r t bufferCap targetCap Q G x A)
    {degree inter neighbors exceptionFlags exceptionList : ℕ → ℕ}
    (hactiveA : I.σ.arrs "activeA" = arrOf n (setFlag A))
    (hdegree : I.σ.arrs "degree" = arrOf n degree)
    (hinter : I.σ.arrs "inter" = arrOf n inter)
    (hneighbors : I.σ.arrs "neighbors" = arrOf n neighbors)
    (hexceptionFlags : I.σ.arrs "exceptionFlags" = arrOf n exceptionFlags)
    (hexceptionList : I.σ.arrs "exceptionList" = arrOf n exceptionList)
    (hnearBound : I.σ.vars "nearBound" = k / 3)
    (hexceptionCap : I.σ.vars "exceptionCap" = cap)
    (hnB : 2 * n + 1 < B) (hkB : k / 3 < B) (hcapB : cap < B) :
    ∃ (σsel σ' : Env) (tape : Fin (r * t) → Fin (Nat.clog 2 m) → Bool)
      (tail : List Bool) (values : List (Fin m)) (used : ℕ)
      (drawFailed : Bool) (stageCost : ℕ),
      I.bits = tapeBits tape ++ tail ∧
      DrawTrace m I.hmPos t r (List.ofFn tape) values used drawFailed ∧
      Run B initialSamplerAttempt I.σ σsel
        (2 + initialDrawSampleCost n m used
          (values.length + if drawFailed then 1 else 0) values.length drawFailed +
          (if drawFailed then 5 else 4 + stageCost)) ∧
      Run B fullInitialAttempt I.σ σ'
        (2 + initialDrawSampleCost n m used
          (values.length + if drawFailed then 1 else 0) values.length drawFailed +
          (if drawFailed then 5 else 4 + stageCost) + 9 +
          (300 * (n + targetCap + 1) + (94 * n + 15) + 8 + (20 * n + 9))) ∧
      σ'.vars "batchFailed" = (if drawFailed then 1 else 0) ∧
      σ'.inp = σsel.inp ∧ σ'.out = σsel.out ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.arrs "activeA" = arrOf n (setFlag A) ∧
      σ'.arrs "activeB" = arrOf n I.activeB ∧
      σ'.vars "n" = n ∧
      (drawFailed = true → σ' = σsel ∧ σ'.vars "attemptAccepted" = 0 ∧
        σ'.arrs "sampleFlags" = arrOf n (fun _ => 0) ∧
        σ'.vars "sampleCount" = 0) ∧
      (drawFailed = false →
        ∃ (W : Finset ℕ) (repFailed : Bool) (repUsed : ℕ),
          W = (values.map (fun i => I.domain i.val)).toFinset ∧
          W ⊆ A ∧ values.length = r ∧
          σsel.vars "repFailed" = (if repFailed then 1 else 0) ∧
          σ'.inp = (I.bits.drop (used * Nat.clog 2 m + repUsed)).map
            Bool.toNat ++ I.rest ∧
          (repFailed = true → σ' = σsel ∧ σ'.vars "attemptAccepted" = 0 ∧
            σ'.arrs "sampleFlags" = arrOf n (setFlag W) ∧
            σ'.vars "sampleCount" = W.card) ∧
          (repFailed = false →
            ∃ (mapped : ℕ → ℕ) (choice : InitialChoice A
                (activeVertices n I.activeB)
                (fun b => numericNeighborhood G b ∩ A) r)
              (packedExceptions packedSample : ℕ → ℕ),
              σsel.arrs "repB" = arrOf n mapped ∧
              choice.draws = values.map (fun i => I.domain i.val) ∧
              choice.sample = W ∧
              (∀ b ∈ activeVertices n I.activeB,
                choice.representative b = mapped b) ∧
              Run B initialAttemptAcceptance σsel σ'
                (300 * (n + targetCap + 1) + (94 * n + 15) + 8 + (20 * n + 9)) ∧
              attemptExceptions n (k / 3) x A (activeVertices n I.activeB) mapped =
                choice.exceptions k ∧
              σ'.arrs "exceptionFlags" =
                arrOf n (setFlag (choice.exceptions k)) ∧
              σ'.arrs "exceptionList" = arrOf n packedExceptions ∧
              PrefixEnumerates (σ'.vars "exceptionCount") packedExceptions
                (choice.exceptions k) ∧
              σ'.vars "exceptionCount" = (choice.exceptions k).card ∧
              σ'.vars "attemptAccepted" =
                (if (choice.exceptions k).card ≤ cap then 1 else 0) ∧
              σ'.arrs "sampleFlags" = arrOf n (setFlag W) ∧
              σ'.arrs "ord" = arrOf n packedSample ∧
              PrefixEnumerates (σ'.vars "sampleCount") packedSample W ∧
              σ'.vars "sampleCount" = W.card ∧
              σ'.arrs "repB" = arrOf n mapped ∧
              σ'.arrs "activeB" = arrOf n (setFlag (activeVertices n I.activeB)) ∧
              σ'.inp = (I.bits.drop (used * Nat.clog 2 m + repUsed)).map
                Bool.toNat ++ I.rest)) := by
  obtain ⟨_σd, σsel, tape, tail, values, used, drawFailed, stageCost,
    hbits, hdrawTrace, hsel, hacceptSel, hnSel, _hqSel, hbatchSel,
    harrayFrame, hvarFrame, hdrawFailure, hdrawSuccess⟩ :=
      initialSamplerAttempt_run_bits I
  let selectionCost := 2 + initialDrawSampleCost n m used
    (values.length + if drawFailed then 1 else 0) values.length drawFailed +
    (if drawFailed then 5 else 4 + stageCost)
  let suffixCost := 300 * (n + targetCap + 1) + (94 * n + 15) + 8 + (20 * n + 9)
  have hbatchGuard :
      (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σsel =
        some (!drawFailed) := guard_eval hbatchSel I.honeB
  have hoffSel : σsel.arrs "off" = arrOf (n + 1) (offset x) := by
    rw [harrayFrame "off" (by decide)]
    exact I.hoff
  have htargetSel : σsel.arrs "tgt" = arrOf targetCap (target x) := by
    rw [harrayFrame "tgt" (by decide)]
    exact I.htarget
  have hactiveASel : σsel.arrs "activeA" = arrOf n (setFlag A) := by
    rw [harrayFrame "activeA" (by decide)]
    exact hactiveA
  have hactiveBSelRaw : σsel.arrs "activeB" = arrOf n I.activeB := by
    rw [harrayFrame "activeB" (by decide)]
    exact I.hactiveB
  have hnearSel : σsel.vars "nearBound" = k / 3 := by
    rw [hvarFrame "nearBound" (by decide)]
    exact hnearBound
  have hcapSel : σsel.vars "exceptionCap" = cap := by
    rw [hvarFrame "exceptionCap" (by decide)]
    exact hexceptionCap
  cases drawFailed with
  | true =>
      have hfalse : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σsel =
          some false := by simpa using hbatchGuard
      have hguard : Run B
          (.ite (.eq (.var "batchFailed") (.lit 0))
            (.ite (.eq (.var "repFailed") (.lit 0)) initialAttemptAcceptance .skip)
            .skip) σsel σsel 5 := by
        simpa [Cond.size, Expr.size] using
          (Run.ite_false hfalse (Run.skip : Run B .skip σsel σsel 1))
      have hfull : Run B fullInitialAttempt I.σ σsel
          (selectionCost + 9 + suffixCost) := by
        have hbound : selectionCost + 5 ≤ selectionCost + 9 + suffixCost := by omega
        simpa [fullInitialAttempt, selectionCost, suffixCost] using
          (hsel.seq hguard).mono hbound
      refine ⟨σsel, σsel, tape, tail, values, used, true, stageCost,
        hbits, hdrawTrace, hsel, hfull, hbatchSel, rfl, rfl,
        hoffSel, htargetSel, hactiveASel, hactiveBSelRaw, hnSel, ?_, ?_⟩
      · intro _
        obtain ⟨_, hflags, hcount⟩ := hdrawFailure rfl
        exact ⟨rfl, hacceptSel, hflags, hcount⟩
      · intro h; cases h
  | false =>
      obtain ⟨W, sampleOrd, sampleCount, σp, q, label, size, xs, sorted,
        repValues, repUsed, repCharge, repFailed, hW, hWA, _hWcard,
        hvaluesLen, _hprefix, _hpartRun, _hsizes, _hoccupied, hclasses,
        _hrepRun, _hnFinal, _hqFinal, hsampleCountSel, _hclassB, _hclassSize,
        hordSel, _hnodup, hxs, _htrace, hrepVal, _hrepFailure,
        hsampleFlagsSel, hinpSel, hrepSuccess, _hstageCost⟩ :=
          hdrawSuccess rfl
      cases repFailed with
      | true =>
          have hrepGuard : (Cond.eq (.var "repFailed") (.lit 0)).evalB B σsel =
              some false := by simpa using guard_eval hrepVal I.honeB
          have hinner : Run B
              (.ite (.eq (.var "repFailed") (.lit 0))
                initialAttemptAcceptance .skip) σsel σsel 5 := by
            simpa [Cond.size, Expr.size] using
              (Run.ite_false hrepGuard (Run.skip : Run B .skip σsel σsel 1))
          have htrue : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σsel =
              some true := by simpa using hbatchGuard
          have hguard : Run B
              (.ite (.eq (.var "batchFailed") (.lit 0))
                (.ite (.eq (.var "repFailed") (.lit 0)) initialAttemptAcceptance .skip)
                .skip) σsel σsel 9 := by
            simpa [Cond.size, Expr.size] using
              (Run.ite_true (d := .skip) htrue hinner)
          have hfull : Run B fullInitialAttempt I.σ σsel
              (selectionCost + 9 + suffixCost) := by
            have hbound : selectionCost + 9 ≤ selectionCost + 9 + suffixCost := by omega
            simpa [fullInitialAttempt, selectionCost, suffixCost] using
              (hsel.seq hguard).mono hbound
          refine ⟨σsel, σsel, tape, tail, values, used, false, stageCost,
            hbits, hdrawTrace, hsel, hfull, hbatchSel, rfl, rfl,
            hoffSel, htargetSel, hactiveASel, hactiveBSelRaw, hnSel, ?_, ?_⟩
          · intro h; cases h
          · intro _
            refine ⟨W, true, repUsed, hW, hWA, hvaluesLen, hrepVal,
              hinpSel, ?_, ?_⟩
            · intro _
              refine ⟨rfl, hacceptSel, ?_, hsampleCountSel⟩
              change σsel.arrs "sampleFlags" =
                arrOf n (fun v => if v ∈ W then 1 else 0)
              exact hsampleFlagsSel
            · intro h; cases h
      | false =>
          obtain ⟨mapped, hmappedArr, _hvFinal, hformula, hrepClass⟩ :=
            hrepSuccess rfl
          let C := activeVertices n I.activeB
          have hCrange : C ⊆ Finset.range n := by
            intro v hv
            exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
          have hrepC : ∀ b ∈ C, mapped b ∈ C := by
            intro b hb
            have hbN := (mem_activeVertices.mp hb).1
            have hbAct := (mem_activeVertices.mp hb).2
            change mapped b ∈ activeVertices n I.activeB
            rw [← hxs]
            exact List.mem_toFinset.mpr (hrepClass b hbN hbAct).2.1
          have hrepN : ∀ b ∈ C, mapped b < n := by
            intro b hb
            exact (mem_activeVertices.mp (hrepC b hb)).1
          have hformula' : ∀ b ∈ C,
              mapped b = writeClassReps sorted I.repClass 0 repValues (label b) := by
            intro b hb
            obtain ⟨hbN, hbAct⟩ := mem_activeVertices.mp hb
            exact hformula b hbN hbAct
          have hrepLabel : ∀ b ∈ C, label (mapped b) = label b := by
            intro b hb
            obtain ⟨hbN, hbAct⟩ := mem_activeVertices.mp hb
            exact (hrepClass b hbN hbAct).2.2
          let draws := values.map (fun i => I.domain i.val)
          have hdrawsLen : draws.length = r := by simp [draws, hvaluesLen]
          have hdrawsMem : ∀ a ∈ draws, a ∈ A := by
            intro a ha
            apply hWA
            rw [hW]
            exact List.mem_toFinset.mpr ha
          obtain ⟨choice, hchoiceDraws, hchoiceSample, hchoiceRep⟩ :=
            initialChoice_of_actual draws W label mapped
              (fun d => writeClassReps sorted I.repClass 0 repValues d)
              hdrawsLen hdrawsMem (by simpa [draws] using hW)
              hclasses hrepC hrepLabel hformula'
          have hactiveBSel : σsel.arrs "activeB" = arrOf n (setFlag C) := by
            rw [harrayFrame "activeB" (by decide), I.hactiveB]
            exact bounded_active_flags_eq_setFlag I.hactive01
          have hdegreeSel : σsel.arrs "degree" = arrOf n degree := by
            rw [harrayFrame "degree" (by decide)]
            exact hdegree
          have hinterSel : σsel.arrs "inter" = arrOf n inter := by
            rw [harrayFrame "inter" (by decide)]
            exact hinter
          have hneighborsSel : σsel.arrs "neighbors" = arrOf n neighbors := by
            rw [harrayFrame "neighbors" (by decide)]
            exact hneighbors
          have hexceptionFlagsSel : σsel.arrs "exceptionFlags" =
              arrOf n exceptionFlags := by
            rw [harrayFrame "exceptionFlags" (by decide)]
            exact hexceptionFlags
          have hexceptionListSel : σsel.arrs "exceptionList" =
              arrOf n exceptionList := by
            rw [harrayFrame "exceptionList" (by decide)]
            exact hexceptionList
          have hstampLen : (σsel.arrs "stamp").length = n := by
            rw [run_array_length_eq hsel "stamp", I.hstamp]
            simp [arrOf]
          obtain ⟨stamp', hstampSel⟩ := exists_arrOf_of_length hstampLen
          have hsampleFlagExact : σsel.arrs "sampleFlags" =
              arrOf n (setFlag W) := by
            change σsel.arrs "sampleFlags" =
              arrOf n (fun v => if v ∈ W then 1 else 0)
            exact hsampleFlagsSel
          obtain ⟨σ', packedExceptions, packedSample, hsuffix,
            hflags, hlist, hprefixE, hcountE, hacceptE, hsampleFlags,
            hord, hprefixW, hcountW, _hdist, hrep, _hactiveA,
            hactiveB, _hoff, _htarget, _hnear, _hcap, _hn,
            _harrFrame, _hvarFrame, hinp, hout⟩ :=
              initialAttemptAcceptance_run I.hx I.htargetCapEq I.hA hCrange
                (hWA.trans I.hA) hWA hrepN hrepC hnSel hnearSel hcapSel
                hoffSel htargetSel hactiveASel hactiveBSel hmappedArr
                hdegreeSel hinterSel hstampSel hneighborsSel hsampleFlagExact
                hordSel hexceptionFlagsSel hexceptionListSel hnB I.htargetCapB
                hkB hcapB
          have hEeq : attemptExceptions n (k / 3) x A C mapped =
              choice.exceptions k := by
            rw [attemptExceptions_div_three_eq I.hx I.htargetCapEq
              A C hCrange mapped hrepN hrepC]
            apply Finset.filter_congr
            intro b hb
            rw [hchoiceRep b hb]
          have hrepGuard : (Cond.eq (.var "repFailed") (.lit 0)).evalB B σsel =
              some true := by simpa using guard_eval hrepVal I.honeB
          have hinner : Run B
              (.ite (.eq (.var "repFailed") (.lit 0))
                initialAttemptAcceptance .skip) σsel σ' (4 + suffixCost) := by
            simpa [suffixCost, Cond.size, Expr.size] using
              (Run.ite_true (d := .skip) hrepGuard hsuffix)
          have hbatchTrue : (Cond.eq (.var "batchFailed") (.lit 0)).evalB B σsel =
              some true := by simpa using hbatchGuard
          have hguard : Run B
              (.ite (.eq (.var "batchFailed") (.lit 0))
                (.ite (.eq (.var "repFailed") (.lit 0)) initialAttemptAcceptance .skip)
                .skip) σsel σ' (8 + suffixCost) := by
            convert (Run.ite_true (d := .skip) hbatchTrue hinner) using 1
            simp only [Cond.size, Expr.size, Nat.reduceAdd]
            omega
          have hfull : Run B fullInitialAttempt I.σ σ'
              (selectionCost + 9 + suffixCost) := by
            have hbound : selectionCost + (8 + suffixCost) ≤
                selectionCost + 9 + suffixCost := by omega
            simpa [fullInitialAttempt, selectionCost, suffixCost] using
              (hsel.seq hguard).mono hbound
          have hbatchFinal : σ'.vars "batchFailed" = 0 := by
            rw [hsuffix.frame_var "batchFailed" (by decide)]
            exact hbatchSel
          have hoffFinal : σ'.arrs "off" = arrOf (n + 1) (offset x) :=
            (hsuffix.frame_arr "off" (by decide)).trans hoffSel
          have htargetFinal : σ'.arrs "tgt" = arrOf targetCap (target x) :=
            (hsuffix.frame_arr "tgt" (by decide)).trans htargetSel
          have hactiveAFinal : σ'.arrs "activeA" = arrOf n (setFlag A) :=
            (hsuffix.frame_arr "activeA" (by decide)).trans hactiveASel
          have hactiveBFinalRaw : σ'.arrs "activeB" = arrOf n I.activeB :=
            (hsuffix.frame_arr "activeB" (by decide)).trans hactiveBSelRaw
          have hnFinal : σ'.vars "n" = n :=
            (hsuffix.frame_var "n" (by decide)).trans hnSel
          refine ⟨σsel, σ', tape, tail, values, used, false, stageCost,
            hbits, hdrawTrace, hsel, hfull, hbatchFinal, hinp, hout,
            hoffFinal, htargetFinal, hactiveAFinal, hactiveBFinalRaw, hnFinal, ?_, ?_⟩
          · intro h; cases h
          · intro _
            refine ⟨W, false, repUsed, hW, hWA, hvaluesLen, hrepVal,
              hinp.trans hinpSel, ?_, ?_⟩
            · intro h; cases h
            · intro _
              refine ⟨mapped, choice, packedExceptions, packedSample,
                hmappedArr, ?_, hchoiceSample, ?_, hsuffix, hEeq,
                ?_, hlist, ?_, ?_, ?_, hsampleFlags, hord,
                hprefixW, hcountW, hrep, hactiveB, ?_⟩
              · exact hchoiceDraws
              · intro b hb; exact hchoiceRep b hb
              · rw [hflags, exception_flags_eq_setFlag, hEeq]
              · simpa only [hEeq] using hprefixE
              · simpa only [hEeq] using hcountE
              · simpa only [hEeq] using hacceptE
              · exact hinp.trans hinpSel

end

end Lax457868Proofs.FullInitialAttempt
