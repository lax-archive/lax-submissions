import Lax457868Proofs.LocalRepairSource
import Lax457868Proofs.RepairFilterSource
import Mathlib.Tactic

/-! One fixed bounded retry loop for the concrete local repair trial. -/

namespace Lax457868Proofs.LocalRepairRetriesSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.LocalRepairSource
open Lax457868Proofs.DrawLogSetup
open Lax457868Proofs.RepairFilterSource
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.RepairClassScan
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases
open Lax11.GraphEncoding
open scoped symmDiff

noncomputable section

set_option maxHeartbeats 2000000

/-- A rejected trial preserves every fixed class and domain input. Length
preservation suffices for the scratch arrays overwritten by the scan. -/
private def ReadyInput.afterRejected
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    {σ' : Env} {K : ℕ}
    (r : Run B (localRepairTrial.seq
      (.assign "repairRetriesLeft"
        (.sub (.var "repairRetriesLeft") (.lit 1)))) R.σ σ' K)
    (newBits : List Bool)
    (hinp : σ'.inp = newBits.map Bool.toNat ++ R.rest)
    (hn : σ'.vars "n" = n)
    (hqpow : σ'.vars "qpow" = R.σ.vars "qpow")
    (hflags : σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))
    (htrial : σ'.arrs "trialActive" = arrOf n (fun _ => 0))
    (hrow : σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hdesired : σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0)) :
    ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent := by
  exact {
    R with
    σ := σ'
    bits := newBits
    hinput := hinp
    hn := hn
    hqpow := by rw [hqpow]; exact R.hqpow
    hmodulus := (r.frame_var "drawModulus" (by decide)).trans R.hmodulus
    htarget := (r.frame_var "batchTarget" (by decide)).trans R.htarget
    hcap := (r.frame_var "drawCap" (by decide)).trans R.hcap
    hrepairB := (r.frame_var "repairB" (by decide)).trans R.hrepairB
    hclassCount := (r.frame_var "classCount" (by decide)).trans R.hclassCount
    hkeyLength := by rw [run_array_length_eq r "key0", R.hkeyLength]
    hdrawsLength := by rw [run_array_length_eq r "sampleDraws", R.hdrawsLength]
    hsample := hflags
    htrialZero := htrial
    hrowZero := hrow
    hdesiredZero := hdesired
    hrowLength := by rw [run_array_length_eq r "trialRowList", R.hrowLength]
    hdesiredLength := by
      rw [run_array_length_eq r "trialDesiredList", R.hdesiredLength]
    hdiffLength := by rw [run_array_length_eq r "trialDiffList", R.hdiffLength]
    hdomain := (r.frame_arr "drawDomain" (by decide)).trans R.hdomain
    hclassB := (r.frame_arr "classB" (by decide)).trans R.hclassB
    hclassSize := (r.frame_arr "classSize" (by decide)).trans R.hclassSize
    hclassStart :=
      (r.frame_arr "repairClassStart" (by decide)).trans R.hclassStart
    hord := (r.frame_arr "ord" (by decide)).trans R.hord
    hoff := (r.frame_arr "off" (by decide)).trans R.hoff
    htgt := (r.frame_arr "tgt" (by decide)).trans R.htgt
    hgroupActive := (r.frame_arr "activeB" (by decide)).trans R.hgroupActive
  }

private lemma runWhileTrue {B : ℕ} {b : Cond} {c : Com}
    {σ σ₁ σ₂ : Env} {P Q : ℕ}
    (hb : b.evalB B σ = some true)
    (hbody : Run B c σ σ₁ P)
    (hloop : Run B (.while b c) σ₁ σ₂ Q) :
    Run B (.while b c) σ σ₂ (1 + b.size + P + Q) := by
  obtain ⟨k, hk, hbs⟩ := hbody
  obtain ⟨k', hk', hbs'⟩ := hloop
  exact ⟨1 + b.size + k + k', by omega,
    BigStepB.while_true hb hbs hbs'⟩

private lemma eq_zero_eval {B : ℕ} {σ : Env} {v : String} {z : ℕ}
    (hz : σ.vars v = z) (hzB : z < B) (hzero : 0 < B) :
    (Cond.eq (.var v) (.lit 0)).evalB B σ = some (z == 0) := by
  have hvar : (Expr.var v).evalB B σ = some z := by
    rw [evalB_var_iff]
    exact ⟨hz.symm, by rw [hz]; exact hzB⟩
  rw [evalB_condEq hvar (evalB_lit hzero)]

private lemma empty_loop_run {B : ℕ} {σ : Env}
    (hstatus : σ.vars "repairRetryStatus" = 0)
    (hleft : σ.vars "repairRetriesLeft" = 0)
    (h3B : 3 < B) :
    Run B (.while (.eq (.var "repairRetryStatus") (.lit 0))
      localRepairRetryBody) σ (σ.setVar "repairRetryStatus" 3) 14 := by
  have hzeroB : 0 < B := by omega
  have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 0)).evalB B σ =
      some true := by simpa using eq_zero_eval hstatus hzeroB hzeroB
  have hleftGuard : (Cond.eq (.var "repairRetriesLeft") (.lit 0)).evalB B σ =
      some true := by simpa using eq_zero_eval hleft hzeroB hzeroB
  have hassign : Run B (.assign "repairRetryStatus" (.lit 3)) σ
      (σ.setVar "repairRetryStatus" 3) 2 := by
    simpa using (Run.assign (x := "repairRetryStatus") (evalB_lit h3B))
  have hbody : Run B localRepairRetryBody σ
      (σ.setVar "repairRetryStatus" 3) 6 := by
    simpa [localRepairRetryBody, Cond.size, Expr.size] using
      (Run.ite_true (d := localRepairTrial.seq _)
        hleftGuard hassign)
  have hstop : (Cond.eq (.var "repairRetryStatus") (.lit 0)).evalB B
      (σ.setVar "repairRetryStatus" 3) = some false := by
    simpa using eq_zero_eval (σ := σ.setVar "repairRetryStatus" 3)
      (v := "repairRetryStatus") (z := 3) (by simp) h3B hzeroB
  have htail : Run B (.while (.eq (.var "repairRetryStatus") (.lit 0))
      localRepairRetryBody) (σ.setVar "repairRetryStatus" 3)
      (σ.setVar "repairRetryStatus" 3) 4 := by
    simpa [Cond.size, Expr.size] using
      (Run.while_false (c := localRepairRetryBody) hstop)
  exact (runWhileTrue hguard hbody htail).mono (by
    simp [Cond.size, Expr.size])

private lemma retry_stop {B : ℕ} {σ : Env} {z : ℕ}
    (hstatus : σ.vars "repairRetryStatus" = z)
    (hzB : z < B) (hzeroB : 0 < B) (hne : z ≠ 0) :
    Run B (.while (.eq (.var "repairRetryStatus") (.lit 0))
      localRepairRetryBody) σ σ 4 := by
  have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 0)).evalB B σ =
      some false := by
    simpa [hne] using eq_zero_eval hstatus hzB hzeroB
  simpa [Cond.size, Expr.size] using
    (Run.while_false (c := localRepairRetryBody) hguard)

private lemma decrement_run {B fuel : ℕ} {σ : Env}
    (hleft : σ.vars "repairRetriesLeft" = fuel + 1)
    (hfuelB : fuel + 1 < B) (honeB : 1 < B) :
    Run B (.assign "repairRetriesLeft"
      (.sub (.var "repairRetriesLeft") (.lit 1)))
      σ (σ.setVar "repairRetriesLeft" fuel) 4 := by
  have hvar : (Expr.var "repairRetriesLeft").evalB B σ = some (fuel + 1) := by
    rw [evalB_var_iff]
    exact ⟨hleft.symm, by rw [hleft]; exact hfuelB⟩
  have hsub : (Expr.sub (.var "repairRetriesLeft") (.lit 1)).evalB B σ =
      some fuel := by
    simpa [Bop.apply] using
      (evalB_bin (op := .sub) hvar (evalB_lit honeB) (by omega : fuel < B))
  simpa using (Run.assign (x := "repairRetriesLeft") hsub)

private lemma retry_body_attempt {B fuel K : ℕ} {σ σa : Env}
    (hleft : σ.vars "repairRetriesLeft" = fuel + 1)
    (hfuelB : fuel + 1 < B) (honeB : 1 < B)
    (rtrial : Run B localRepairTrial σ σa K)
    (hleftA : σa.vars "repairRetriesLeft" = fuel + 1) :
    Run B localRepairRetryBody σ
      (σa.setVar "repairRetriesLeft" fuel) (K + 8) := by
  have hguard : (Cond.eq (.var "repairRetriesLeft") (.lit 0)).evalB B σ =
      some false := by
    simpa using eq_zero_eval hleft hfuelB (by omega : 0 < B)
  have rdec := decrement_run hleftA hfuelB honeB
  have hseq := rtrial.seq rdec
  have hr := Run.ite_false
    (c := Com.assign "repairRetryStatus" (.lit 3)) hguard hseq
  simpa [localRepairRetryBody] using
    (hr.mono (by simp [Cond.size, Expr.size]; omega))

/-- The fixed while-command consumes at most `fuel` trials. Every successful
trial contributes exactly `s` draws in the unchanged domain, while rejection
and capped random-draw failure leave the current sample untouched. -/
lemma localRepairWhile_run
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (fuel : ℕ)
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    (hstatus : R.σ.vars "repairRetryStatus" = 0)
    (hleft : R.σ.vars "repairRetriesLeft" = fuel)
    (hL : R.σ.vars "L" = Nat.clog 2 m)
    (hv : R.σ.vars "v" = b)
    (hfuelB : fuel < B)
    (hbudget : fuel * (s * t * Nat.clog 2 m) ≤ R.bits.length) :
    ∃ (σ' : Env) (attempts totalUsed : ℕ),
      Run B (.while (.eq (.var "repairRetryStatus") (.lit 0))
        localRepairRetryBody) R.σ σ'
        ((15 * Nat.clog 2 m + 30) * totalUsed +
          attempts * (79 * s + R.scanUpper + 50) + 14) ∧
      attempts ≤ fuel ∧ totalUsed ≤ attempts * (s * t) ∧
      σ'.inp = (R.bits.drop (totalUsed * Nat.clog 2 m)).map Bool.toNat ++ R.rest ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = R.σ.vars "qpow" ∧
      σ'.arrs "trialActive" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      ((σ'.vars "repairRetryStatus" = 1 ∧
          ∃ D : List ℕ, D.length = s ∧ (∀ v ∈ D, v ∈ X) ∧
            localTrialIsolates (numericNeighborhood G) groupedB Wbase b D ∧
            σ'.arrs "sampleFlags" = arrOf n (setFlag (Wcurrent ∪ D.toFinset))) ∨
        (σ'.vars "repairRetryStatus" = 2 ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) ∨
        (σ'.vars "repairRetryStatus" = 3 ∧ attempts = fuel ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) := by
  induction fuel generalizing R with
  | zero =>
    let σ' := R.σ.setVar "repairRetryStatus" 3
    have rr := empty_loop_run hstatus hleft R.hthreeB
    refine ⟨σ', 0, 0, ?_, by omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [σ'] using rr
    · simpa [σ'] using R.hinput
    · simpa [σ'] using R.hn
    · simpa [σ'] using R.hqpow
    · simpa [σ'] using R.htrialZero
    · simpa [σ'] using R.hrowZero
    · simpa [σ'] using R.hdesiredZero
    · right; right
      simp [σ', R.hsample]
  | succ fuel ih =>
    let L := Nat.clog 2 m
    let C := 15 * L + 30
    let A := 79 * s + R.scanUpper + 50
    have hbudgetOne : s * t * L ≤ R.bits.length := by
      dsimp [L] at *
      calc
        s * t * Nat.clog 2 m ≤ (fuel + 1) * (s * t * Nat.clog 2 m) := by
          apply Nat.le_mul_of_pos_left
          omega
        _ ≤ R.bits.length := hbudget
    obtain ⟨values, used, failed, σa, rtrial, hused, hcomplete,
      hinp, hX, htrial, hrow, hdesired, hn, hqpow,
      hfail, hstatusLe, hsuccess⟩ :=
      localRepairTrial_run_bits R hL hv hbudgetOne
    let D := values.map (fun i => R.domain i.val)
    let K := C * used + 79 * s + R.scanCharge D + 38
    have rtrial' : Run B localRepairTrial R.σ σa K := by
      simpa [K, C, L, D] using rtrial
    have hleftA : σa.vars "repairRetriesLeft" = fuel + 1 := by
      rw [(rtrial'.frame_var "repairRetriesLeft" (by decide))]
      exact hleft
    have rbody := retry_body_attempt hleft hfuelB (by omega : 1 < B)
      rtrial' hleftA
    let σb := σa.setVar "repairRetriesLeft" fuel
    have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 0)).evalB B R.σ =
        some true := by
      simpa using eq_zero_eval hstatus (by omega : 0 < B)
        (by omega : 0 < B)
    have hcharge : R.scanCharge D ≤ R.scanUpper := R.scanCharge_le D
    have hinputB : σb.inp =
        (R.bits.drop (used * L)).map Bool.toNat ++ R.rest := by
      simpa [σb, L] using hinp
    have hnB : σb.vars "n" = n := by simpa [σb] using hn
    have hqpowB : σb.vars "qpow" = R.σ.vars "qpow" := by
      simpa [σb] using hqpow
    have htrialB : σb.arrs "trialActive" = arrOf n (fun _ => 0) := by
      simpa [σb] using htrial
    have hrowB : σb.arrs "trialRowMarks" = arrOf n (fun _ => 0) := by
      simpa [σb] using hrow
    have hdesiredB : σb.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) := by
      simpa [σb] using hdesired
    have hstatusB : σb.vars "repairRetryStatus" =
        σa.vars "repairRetryStatus" := by simp [σb]
    have hflagsB : σb.arrs "sampleFlags" = σa.arrs "sampleFlags" := by
      simp [σb]
    by_cases hfailed : failed = true
    · obtain ⟨hstatusA, hflagsA⟩ := hfail hfailed
      have hstatus2 : σb.vars "repairRetryStatus" = 2 := by
        rw [hstatusB]; exact hstatusA
      have rstop := retry_stop hstatus2 (by have := R.hthreeB; omega : 2 < B)
        (by omega : 0 < B) (by decide)
      have rr := runWhileTrue hguard rbody rstop
      refine ⟨σb, 1, used, ?_, by omega, ?_, hinputB, hnB,
        hqpowB, htrialB, hrowB, hdesiredB, ?_⟩
      · apply rr.mono
        dsimp [K, C, A, L]
        omega
      · simpa using hused
      · right; left
        exact ⟨hstatus2, by rw [hflagsB]; exact hflagsA⟩
    · have hfalse : failed = false := Bool.eq_false_iff.mpr hfailed
      have hlen : D.length = s := by simpa [D] using hcomplete hfalse
      have hle := hstatusLe hfalse
      rcases Nat.eq_zero_or_pos (σa.vars "repairRetryStatus") with hzero | hpos
      · obtain ⟨_, _, hreject⟩ := hsuccess hfalse
        have hflagsA := hreject hzero
        have hflagsB' : σb.arrs "sampleFlags" = arrOf n (setFlag Wcurrent) := by
          rw [hflagsB]; exact hflagsA
        have rdec := decrement_run hleftA hfuelB (by omega : 1 < B)
        have rseq : Run B
            (localRepairTrial.seq (.assign "repairRetriesLeft"
              (.sub (.var "repairRetriesLeft") (.lit 1))))
            R.σ σb (K + 4) := by
          simpa [σb] using rtrial'.seq rdec
        let Rnext := ReadyInput.afterRejected R rseq (R.bits.drop (used * L))
          (by simpa [L] using hinputB) hnB hqpowB hflagsB'
          htrialB hrowB hdesiredB
        have hstatusNext : Rnext.σ.vars "repairRetryStatus" = 0 := by
          change σb.vars "repairRetryStatus" = 0
          rw [hstatusB]
          exact hzero
        have hleftNext : Rnext.σ.vars "repairRetriesLeft" = fuel := by
          change σb.vars "repairRetriesLeft" = fuel
          simp [σb]
        have hLnext : Rnext.σ.vars "L" = L := by
          change σb.vars "L" = L
          simpa [σb] using
            ((rtrial'.frame_var "L" (by decide)).trans hL)
        have hvnext : Rnext.σ.vars "v" = b := by
          change σb.vars "v" = b
          simpa [σb] using
            ((rtrial'.frame_var "v" (by decide)).trans hv)
        have hbudgetNext : fuel * (s * t * L) ≤ Rnext.bits.length := by
          change fuel * (s * t * L) ≤ (R.bits.drop (used * L)).length
          rw [List.length_drop]
          have husedL : used * L ≤ s * t * L := Nat.mul_le_mul_right _ hused
          have hbudget' : fuel * (s * t * L) + (s * t * L) ≤
              R.bits.length := by
            convert hbudget using 1 <;> simp [L, Nat.add_mul, Nat.mul_add]
          omega
        have hfuelNext : fuel < B := by omega
        obtain ⟨σ', attempts', totalUsed', rrec, hattempts', htotalUsed',
          hinp', hn', hqpow', htrial', hrow', hdesired', hout'⟩ :=
          ih Rnext hstatusNext hleftNext hLnext hvnext hfuelNext
            (by simpa [L] using hbudgetNext)
        have hinputFinal : σ'.inp =
            (R.bits.drop ((used + totalUsed') * L)).map Bool.toNat ++ R.rest := by
          change σ'.inp =
            ((R.bits.drop (used * L)).drop (totalUsed' * L)).map Bool.toNat ++
              R.rest at hinp'
          simpa [L, Nat.add_mul, List.drop_drop] using hinp'
        have htotal : used + totalUsed' ≤ (attempts' + 1) * (s * t) := by
          calc
            used + totalUsed' ≤ s * t + attempts' * (s * t) := by omega
            _ = (attempts' + 1) * (s * t) := by ring
        have hqpowFinal : σ'.vars "qpow" = R.σ.vars "qpow" := by
          simpa [Rnext, σb] using hqpow'.trans hqpowB
        have hUpper : Rnext.scanUpper = R.scanUpper := rfl
        have rrec' : Run B (.while (.eq (.var "repairRetryStatus") (.lit 0))
            localRepairRetryBody) σb σ'
            (C * totalUsed' + attempts' * A + 14) := by
          change Run B (.while (.eq (.var "repairRetryStatus") (.lit 0))
            localRepairRetryBody) σb σ'
            ((15 * Nat.clog 2 m + 30) * totalUsed' +
              attempts' * (79 * s + Rnext.scanUpper + 50) + 14) at rrec
          simpa [C, A, L, hUpper] using rrec
        refine ⟨σ', attempts' + 1, used + totalUsed', ?_, by omega,
          htotal, ?_, hn', hqpowFinal, htrial', hrow', hdesired', ?_⟩
        · apply (runWhileTrue hguard rbody rrec').mono
          dsimp [Cond.size, Expr.size]
          change 4 + (K + 8) + (C * totalUsed' + attempts' * A + 14) ≤
            C * (used + totalUsed') + (attempts' + 1) * A + 14
          dsimp [K, A]
          nlinarith [hcharge]
        · simpa [Nat.clog, L] using hinputFinal
        · rcases hout' with hsuccess' | hfailure' | hexhaust'
          · left
            obtain ⟨hz, D', hD'⟩ := hsuccess'
            refine ⟨hz, D', ?_⟩
            simpa [Rnext] using hD'
          · right; left
            exact ⟨hfailure'.1, by simpa [Rnext] using hfailure'.2⟩
          · right; right
            exact ⟨hexhaust'.1, by omega,
              by simpa [Rnext] using hexhaust'.2.2⟩
      · have hstatus1 : σa.vars "repairRetryStatus" = 1 := by omega
        obtain ⟨hiff, haccept, _⟩ := hsuccess hfalse
        have hflagsA := haccept hstatus1
        have hstatus1B : σb.vars "repairRetryStatus" = 1 := by
          rw [hstatusB]; exact hstatus1
        have rstop := retry_stop hstatus1B (by omega : 1 < B)
          (by omega : 0 < B) (by decide)
        have rr := runWhileTrue hguard rbody rstop
        refine ⟨σb, 1, used, ?_, by omega, ?_, hinputB, hnB,
          hqpowB, htrialB, hrowB, hdesiredB, ?_⟩
        · apply rr.mono
          dsimp [K, C, A, L]
          omega
        · simpa using hused
        · left
          refine ⟨hstatus1B, D, hlen, ?_, (hiff.mp hstatus1), ?_⟩
          · simpa [D] using hX
          · rw [hflagsB]
            exact hflagsA

/-- The full one-exception source initializes its retry register, computes the
draw width once, and runs the bounded while-command. The returned bit suffix
is exact; the charge includes logarithm setup once and only used draw bits
thereafter. -/
lemma localRepairRetriesSource_run
    {B n m domainCap s t bufferCap targetCap q b cap : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    (hcap : R.σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ R.bits.length) :
    ∃ (σ' : Env) (attempts totalUsed : ℕ),
      Run B localRepairRetriesSource R.σ σ'
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * totalUsed +
            attempts * (79 * s + R.scanUpper + 50) + 14)) ∧
      attempts ≤ cap ∧ totalUsed ≤ attempts * (s * t) ∧
      σ'.inp = (R.bits.drop (totalUsed * Nat.clog 2 m)).map Bool.toNat ++ R.rest ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = R.σ.vars "qpow" ∧
      σ'.arrs "trialActive" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      ((σ'.vars "repairRetryStatus" = 1 ∧
          ∃ D : List ℕ, D.length = s ∧ (∀ v ∈ D, v ∈ X) ∧
            localTrialIsolates (numericNeighborhood G) groupedB Wbase b D ∧
            σ'.arrs "sampleFlags" = arrOf n (setFlag (Wcurrent ∪ D.toFinset))) ∨
        (σ'.vars "repairRetryStatus" = 2 ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) ∨
        (σ'.vars "repairRetryStatus" = 3 ∧ attempts = cap ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) := by
  let L := Nat.clog 2 m
  let σ₁ := R.σ.setVar "repairRetriesLeft" cap
  let σ₂ := σ₁.setVar "repairRetryStatus" 0
  have r1 : Run B (.assign "repairRetriesLeft" (.var "repairRetryCap"))
      R.σ σ₁ 2 := by
    have heval : (Expr.var "repairRetryCap").evalB B R.σ = some cap := by
      rw [evalB_var_iff]
      exact ⟨hcap.symm, by rw [hcap]; exact hcapB⟩
    simpa [σ₁] using (Run.assign (x := "repairRetriesLeft") heval)
  have r2 : Run B (.assign "repairRetryStatus" (.lit 0)) σ₁ σ₂ 2 := by
    simpa [σ₂] using (Run.assign (x := "repairRetryStatus")
      (evalB_lit (by have := R.hthreeB; omega : 0 < B)))
  have hn2 : σ₂.vars "n" = n := by simp [σ₂, σ₁, R.hn]
  have hq2 : σ₂.vars "qpow" < B := by simpa [σ₂, σ₁] using R.hqpow
  have hm2 : σ₂.vars "drawModulus" = m := by
    simpa [σ₂, σ₁] using R.hmodulus
  obtain ⟨σ₃, rlog, hn3, hq3, hL3, hm3, hcap3,
      hoff3, hv3, harr3, hinp3, hout3⟩ :=
    Lax457868Proofs.DrawLogSetup.drawLogSetup_run
      (B := B) (m := m) (σ := σ₂)
      (by rw [hn2]; have := R.hn1B; omega) hq2 hm2
      R.hmB R.hpowB
  let σ₄ := σ₃.setVar "v" b
  have hrepairB3 : σ₃.vars "repairB" = b := by
    rw [rlog.frame_var "repairB" (by decide)]
    simpa [σ₂, σ₁] using R.hrepairB
  have r4 : Run B (.assign "v" (.var "repairB")) σ₃ σ₄ 2 := by
    have heval : (Expr.var "repairB").evalB B σ₃ = some b := by
      rw [evalB_var_iff]
      exact ⟨hrepairB3.symm, by rw [hrepairB3]; have := R.hbrange; have := R.hn1B; omega⟩
    simpa [σ₄] using (Run.assign (x := "v") heval)
  let repairPrefix : Com := (Com.assign "repairRetriesLeft" (.var "repairRetryCap")).seq
    ((Com.assign "repairRetryStatus" (.lit 0)).seq
      (drawLogSetup.seq (.assign "v" (.var "repairB"))))
  have rprefix : Run B repairPrefix R.σ σ₄ (12 * L + 24) := by
    have r := r1.seq (r2.seq (rlog.seq r4))
    exact r.mono (by dsimp [L]; omega)
  have hq4eq : σ₄.vars "qpow" = R.σ.vars "qpow" := by
    change σ₃.vars "qpow" = R.σ.vars "qpow"
    rw [hq3]
    simp [σ₂, σ₁]
  let Rready : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent := {
    R with
    σ := σ₄
    hinput := by simpa [σ₄, σ₂, σ₁] using hinp3.trans R.hinput
    hn := by simpa [σ₄, hn2] using hn3.trans hn2
    hqpow := by rw [hq4eq]; exact R.hqpow
    hmodulus := (rprefix.frame_var "drawModulus" (by decide)).trans R.hmodulus
    htarget := (rprefix.frame_var "batchTarget" (by decide)).trans R.htarget
    hcap := (rprefix.frame_var "drawCap" (by decide)).trans R.hcap
    hrepairB := (rprefix.frame_var "repairB" (by decide)).trans R.hrepairB
    hclassCount := (rprefix.frame_var "classCount" (by decide)).trans R.hclassCount
    hkeyLength := by rw [run_array_length_eq rprefix "key0", R.hkeyLength]
    hdrawsLength := by rw [run_array_length_eq rprefix "sampleDraws", R.hdrawsLength]
    hsample := (rprefix.frame_arr "sampleFlags" (by decide)).trans R.hsample
    htrialZero := (rprefix.frame_arr "trialActive" (by decide)).trans R.htrialZero
    hrowZero := (rprefix.frame_arr "trialRowMarks" (by decide)).trans R.hrowZero
    hdesiredZero := (rprefix.frame_arr "trialDesiredMarks" (by decide)).trans R.hdesiredZero
    hrowLength := by rw [run_array_length_eq rprefix "trialRowList", R.hrowLength]
    hdesiredLength := by rw [run_array_length_eq rprefix "trialDesiredList", R.hdesiredLength]
    hdiffLength := by rw [run_array_length_eq rprefix "trialDiffList", R.hdiffLength]
    hdomain := (rprefix.frame_arr "drawDomain" (by decide)).trans R.hdomain
    hclassB := (rprefix.frame_arr "classB" (by decide)).trans R.hclassB
    hclassSize := (rprefix.frame_arr "classSize" (by decide)).trans R.hclassSize
    hclassStart := (rprefix.frame_arr "repairClassStart" (by decide)).trans R.hclassStart
    hord := (rprefix.frame_arr "ord" (by decide)).trans R.hord
    hoff := (rprefix.frame_arr "off" (by decide)).trans R.hoff
    htgt := (rprefix.frame_arr "tgt" (by decide)).trans R.htgt
    hgroupActive := (rprefix.frame_arr "activeB" (by decide)).trans R.hgroupActive
  }
  have hstatus4 : Rready.σ.vars "repairRetryStatus" = 0 := by
    change σ₄.vars "repairRetryStatus" = 0
    rw [r4.frame_var "repairRetryStatus" (by decide)]
    rw [rlog.frame_var "repairRetryStatus" (by decide)]
    simp [σ₂]
  have hleft4 : Rready.σ.vars "repairRetriesLeft" = cap := by
    change σ₄.vars "repairRetriesLeft" = cap
    rw [r4.frame_var "repairRetriesLeft" (by decide)]
    rw [rlog.frame_var "repairRetriesLeft" (by decide)]
    simp [σ₂, σ₁]
  have hL4 : Rready.σ.vars "L" = L := by
    change σ₄.vars "L" = L
    simpa [σ₄, L] using hL3
  have hv4 : Rready.σ.vars "v" = b := by
    change σ₄.vars "v" = b
    simp [σ₄]
  obtain ⟨σ', attempts, totalUsed, rloop, hattempts, hused,
    hinp, hn, hq, htrial, hrow, hdesired, hout⟩ :=
    localRepairWhile_run cap Rready hstatus4 hleft4 hL4 hv4 hcapB hbudget
  refine ⟨σ', attempts, totalUsed, ?_, hattempts, hused, hinp,
    hn, ?_, htrial, hrow, hdesired, ?_⟩
  · have hUpperReady : Rready.scanUpper = R.scanUpper := rfl
    rw [hUpperReady] at rloop
    change Run B (.while (.eq (.var "repairRetryStatus") (.lit 0))
      localRepairRetryBody) σ₄ σ'
      ((15 * L + 30) * totalUsed +
        attempts * (79 * s + R.scanUpper + 50) + 14) at rloop
    have r := r1.seq (r2.seq (rlog.seq (r4.seq rloop)))
    apply r.mono
    simp [localRepairRetriesSource, L]
    omega
  · exact hq.trans hq4eq
  · exact hout

/-- The domain filter changes only the prepared draw domain and its modulus.
All fixed Step 2 class data and the accumulated sample survive it. -/
private def ReadyInput.afterDomain
    {B n m s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m n s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    {σ' : Env} {K : ℕ} {domain' : ℕ → ℕ}
    (r : Run B repairDomainSource R.σ σ' K)
    (hdomain : σ'.arrs "drawDomain" = arrOf n domain')
    (hmod : σ'.vars "drawModulus" = m)
    (henum : PrefixEnumerates m domain' X)
    (hn : σ'.vars "n" = n)
    (hsample : σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) :
    ReadyInput B n m n s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent := by
  exact {
    R with
    σ := σ'
    domain := domain'
    hdomain := hdomain
    henum := henum
    hinput := by rw [r.frame_inp (by decide)]; exact R.hinput
    hn := hn
    hqpow := by rw [r.frame_var "qpow" (by decide)]; exact R.hqpow
    hmodulus := hmod
    htarget := (r.frame_var "batchTarget" (by decide)).trans R.htarget
    hcap := (r.frame_var "drawCap" (by decide)).trans R.hcap
    hrepairB := (r.frame_var "repairB" (by decide)).trans R.hrepairB
    hclassCount := (r.frame_var "classCount" (by decide)).trans R.hclassCount
    hkeyLength := by rw [run_array_length_eq r "key0", R.hkeyLength]
    hdrawsLength := by rw [run_array_length_eq r "sampleDraws", R.hdrawsLength]
    hsample := hsample
    htrialZero := (r.frame_arr "trialActive" (by decide)).trans R.htrialZero
    hrowZero := (r.frame_arr "trialRowMarks" (by decide)).trans R.hrowZero
    hdesiredZero := (r.frame_arr "trialDesiredMarks" (by decide)).trans R.hdesiredZero
    hrowLength := by rw [run_array_length_eq r "trialRowList", R.hrowLength]
    hdesiredLength := by rw [run_array_length_eq r "trialDesiredList", R.hdesiredLength]
    hdiffLength := by rw [run_array_length_eq r "trialDiffList", R.hdiffLength]
    hclassB := (r.frame_arr "classB" (by decide)).trans R.hclassB
    hclassSize := (r.frame_arr "classSize" (by decide)).trans R.hclassSize
    hclassStart := (r.frame_arr "repairClassStart" (by decide)).trans R.hclassStart
    hord := (r.frame_arr "ord" (by decide)).trans R.hord
    hoff := (r.frame_arr "off" (by decide)).trans R.hoff
    htgt := (r.frame_arr "tgt" (by decide)).trans R.htgt
    hgroupActive := (r.frame_arr "activeB" (by decide)).trans R.hgroupActive
  }

/-- Complete fixed one-exception command: compute the symmetric-difference
domain, compare its cardinality to the stored far threshold, and run bounded
local retries only in the far case. -/
def localRepairOneExceptionSource : Com :=
  repairDomainSource.seq
    (.ite (.lt (.var "repairFarBound") (.var "drawModulus"))
      localRepairRetriesSource (.assign "repairRetryStatus" (.lit 1)))


/-- Facts available before constructing the repair domain. No draw modulus,
enumeration, or positivity is assumed before the filter runs. -/
structure PreDomainInput (B n s t bufferCap targetCap q b : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ)
    (groupedB Wbase Wcurrent : Finset ℕ) where
  σ : Env
  bits : List Bool
  rest : List ℕ
  size : ℕ → ℕ
  starts : ℕ → ℕ
  label : ℕ → ℕ
  ord : ℕ → ℕ
  groupActive : ℕ → ℕ
  xs : List ℕ
  hgraph : EncodesGraph x n G
  htargetCap : targetCap = 2 * edgeCount x
  hdrawDomainLength : (σ.arrs "drawDomain").length = n
  hinput : σ.inp = bits.map Bool.toNat ++ rest
  hn : σ.vars "n" = n
  hqpow : σ.vars "qpow" < B
  htarget : σ.vars "batchTarget" = s
  hcap : σ.vars "drawCap" = t
  hrepairB : σ.vars "repairB" = b
  hclassCount : σ.vars "classCount" = q
  hkeyLength : (σ.arrs "key0").length = n
  hdrawsLength : (σ.arrs "sampleDraws").length = bufferCap
  hsample : σ.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)
  htrialZero : σ.arrs "trialActive" = arrOf n (fun _ => 0)
  hrowZero : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0)
  hdesiredZero : σ.arrs "trialDesiredMarks" = arrOf n (fun _ => 0)
  hrowLength : (σ.arrs "trialRowList").length = n
  hdesiredLength : (σ.arrs "trialDesiredList").length = n
  hdiffLength : (σ.arrs "trialDiffList").length = n
  hclassB : σ.arrs "classB" = arrOf n label
  hclassSize : σ.arrs "classSize" = arrOf n size
  hclassStart : σ.arrs "repairClassStart" = arrOf n starts
  hord : σ.arrs "ord" = arrOf n ord
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htgt : σ.arrs "tgt" = arrOf targetCap (target x)
  hgroupActive : σ.arrs "activeB" = arrOf n groupActive
  hxsCard : xs.length = (activeVertices n groupActive).card
  hxsRange : xs.toFinset ⊆ Finset.range n
  hactiveCard : (activeVertices n groupActive).card ≤ n
  hslice : ∀ d < q, PrefixEnumerates (size d)
    (fun i => ord (classStart size d + i)) (labelClass xs label d)
  hstartTable : ∀ d < q, starts d = classStart size d
  hclassEnd : ∀ d < q, classStart size d + size d ≤ xs.length
  hclassFibre : labelClass xs label (label b) =
    groupedB.filter (fun v =>
      trace (numericNeighborhood G) Wbase b =
        trace (numericNeighborhood G) Wbase v)
  hbrange : b < n
  hqle : q ≤ n
  hlabel : label b < q
  hWrange : Wcurrent ⊆ Finset.range n
  hWbase : Wbase ⊆ Wcurrent
  hn1B : n + 1 < B
  htargetCapB : targetCap < B
  hbuffer : s ≤ bufferCap
  hsB : s < B
  htB : t < B
  hthreeB : 3 < B

def PreDomainInput.scanUpper
    {B n s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {groupedB Wbase Wcurrent : Finset ℕ}
    (P : PreDomainInput B n s t bufferCap targetCap q b
      G x groupedB Wbase Wcurrent) : ℕ :=
  66 * (offset x (b + 1) - offset x b) +
    repairClassPotential
      (classStart P.size (P.label b) + P.size (P.label b))
      (classStart P.size (P.label b))
      (repairClassSlotWeight x P.ord) + 47

/-- Execute the domain builder from arbitrary `drawDomain` contents of length
`n`, retaining its cleared support marks for the next exception. -/
private lemma preDomain_run
    {B n s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {groupedB Wbase Wcurrent A X : Finset ℕ}
    {rep blist rlist : ℕ → ℕ}
    (P : PreDomainInput B n s t bufferCap targetCap q b
      G x groupedB Wbase Wcurrent)
    (hA : A ⊆ Finset.range n)
    (hrep : P.σ.arrs "repB" = arrOf n rep)
    (hactive : P.σ.arrs "activeA" = arrOf n (setFlag A))
    (hbmarks : P.σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hrmarks : P.σ.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hblist : P.σ.arrs "repairBList" = arrOf n blist)
    (hrlist : P.σ.arrs "repairRList" = arrOf n rlist)
    (hr : rep b < n)
    (hXeq : X = ((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G (rep b) ∩ A))) :
    ∃ (σd : Env) (domain' : ℕ → ℕ),
      Run B repairDomainSource P.σ σd
        (54 * ((offset x (b + 1) - offset x b) +
          (offset x (rep b + 1) - offset x (rep b))) +
          36 * (((numericNeighborhood G b ∩ A).card) +
            ((numericNeighborhood G (rep b) ∩ A).card)) + 73) ∧
      σd.arrs "drawDomain" = arrOf n domain' ∧
      σd.vars "drawModulus" = X.card ∧
      PrefixEnumerates X.card domain' X ∧
      X ⊆ Finset.range n ∧
      σd.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
      σd.arrs "repairRMarks" = arrOf n (fun _ => 0) ∧
      σd.arrs "sampleFlags" = arrOf n (setFlag Wcurrent) ∧
      σd.vars "n" = n ∧ σd.inp = P.σ.inp := by
  obtain ⟨domain, hdomain⟩ := exists_arrOf_of_length P.hdrawDomainLength
  obtain ⟨σd, domain', blist', rlist', rd, hdomain', hmod,
    henum, hXrange, hBmarks, hRmarks, hBlist, hRlist,
    hBLen, hRLen, hrep', hactive', hoff', htgt', hsample,
    hclassB, hclassSize, hord, hstamp, hactiveB, hexceptions,
    hsampleCount, hn, hinp, hout⟩ :=
    repairDomainSource_run P.hgraph P.htargetCap hA P.hn P.hrepairB
      hrep P.hoff P.htgt hactive hbmarks hrmarks hblist hrlist
      hdomain P.hbrange hr P.hn1B P.htargetCapB
  refine ⟨σd, domain', rd, hdomain', ?_, ?_, ?_, hBmarks, hRmarks,
    ?_, hn, hinp⟩
  · simpa [← hXeq] using hmod
  · simpa [hmod, ← hXeq] using henum
  · simpa [hXeq] using hXrange
  · rw [hsample]
    exact P.hsample

/-- The far branch starts with an unprepared draw-domain buffer. The builder
computes its modulus and enumeration; only then does the fixed retry program
use the positive modulus. -/
lemma localRepairOneException_run_far
    {B n s t bufferCap targetCap q b cap k : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {groupedB Wbase Wcurrent A X : Finset ℕ}
    {rep blist rlist : ℕ → ℕ}
    (P : PreDomainInput B n s t bufferCap targetCap q b
      G x groupedB Wbase Wcurrent)
    (hA : A ⊆ Finset.range n)
    (hrep : P.σ.arrs "repB" = arrOf n rep)
    (hactive : P.σ.arrs "activeA" = arrOf n (setFlag A))
    (hbmarks : P.σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hrmarks : P.σ.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hblist : P.σ.arrs "repairBList" = arrOf n blist)
    (hrlist : P.σ.arrs "repairRList" = arrOf n rlist)
    (hr : rep b < n)
    (hXeq : X = ((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G (rep b) ∩ A)))
    (hfar : P.σ.vars "repairFarBound" = (2 * k) / 3)
    (hfarB : (2 * k) / 3 < B)
    (hfarCase : (2 * k) / 3 < X.card)
    (hcap : P.σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hpowB : 2 ^ Nat.clog 2 X.card < B)
    (hbudget : cap * (s * t * Nat.clog 2 X.card) ≤ P.bits.length) :
    ∃ (σ' : Env) (attempts totalUsed : ℕ),
      Run B localRepairOneExceptionSource P.σ σ'
        ((54 * ((offset x (b + 1) - offset x b) +
            (offset x (rep b + 1) - offset x (rep b))) +
            36 * (((numericNeighborhood G b ∩ A).card) +
              ((numericNeighborhood G (rep b) ∩ A).card)) + 73) +
          (4 + (12 * Nat.clog 2 X.card + 24 +
            ((15 * Nat.clog 2 X.card + 30) * totalUsed +
              attempts * (79 * s + P.scanUpper + 50) + 14)))) ∧
      attempts ≤ cap ∧ totalUsed ≤ attempts * (s * t) ∧
      σ'.inp = (P.bits.drop (totalUsed * Nat.clog 2 X.card)).map Bool.toNat ++ P.rest ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = P.σ.vars "qpow" ∧
      σ'.arrs "trialActive" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairRMarks" = arrOf n (fun _ => 0) ∧
      ((σ'.vars "repairRetryStatus" = 1 ∧
          ∃ D : List ℕ, D.length = s ∧ (∀ v ∈ D, v ∈ X) ∧
            localTrialIsolates (numericNeighborhood G) groupedB Wbase b D ∧
            σ'.arrs "sampleFlags" = arrOf n (setFlag (Wcurrent ∪ D.toFinset))) ∨
        (σ'.vars "repairRetryStatus" = 2 ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) ∨
        (σ'.vars "repairRetryStatus" = 3 ∧ attempts = cap ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) := by
  obtain ⟨σd, domain', rd, hdomain, hmod, henum, hXrange,
    hBmarks, hRmarks, hsample, hn, hinpD⟩ :=
    preDomain_run P hA hrep hactive hbmarks hrmarks hblist hrlist hr hXeq
  let Rafter : ReadyInput B n X.card n s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent := {
    σ := σd
    bits := P.bits
    rest := P.rest
    domain := domain'
    size := P.size
    starts := P.starts
    label := P.label
    ord := P.ord
    groupActive := P.groupActive
    xs := P.xs
    hgraph := P.hgraph
    htargetCap := P.htargetCap
    hpositive := by omega
    hdomainCap := Finset.card_le_card hXrange |>.trans (by simp)
    hdomain := hdomain
    henum := henum
    hXrange := hXrange
    hinput := by rw [hinpD]; exact P.hinput
    hn := hn
    hqpow := by rw [rd.frame_var "qpow" (by decide)]; exact P.hqpow
    hmodulus := hmod
    htarget := (rd.frame_var "batchTarget" (by decide)).trans P.htarget
    hcap := (rd.frame_var "drawCap" (by decide)).trans P.hcap
    hrepairB := (rd.frame_var "repairB" (by decide)).trans P.hrepairB
    hclassCount := (rd.frame_var "classCount" (by decide)).trans P.hclassCount
    hkeyLength := by rw [run_array_length_eq rd "key0", P.hkeyLength]
    hdrawsLength := by rw [run_array_length_eq rd "sampleDraws", P.hdrawsLength]
    hsample := hsample
    htrialZero := (rd.frame_arr "trialActive" (by decide)).trans P.htrialZero
    hrowZero := (rd.frame_arr "trialRowMarks" (by decide)).trans P.hrowZero
    hdesiredZero := (rd.frame_arr "trialDesiredMarks" (by decide)).trans P.hdesiredZero
    hrowLength := by rw [run_array_length_eq rd "trialRowList", P.hrowLength]
    hdesiredLength := by rw [run_array_length_eq rd "trialDesiredList", P.hdesiredLength]
    hdiffLength := by rw [run_array_length_eq rd "trialDiffList", P.hdiffLength]
    hclassB := (rd.frame_arr "classB" (by decide)).trans P.hclassB
    hclassSize := (rd.frame_arr "classSize" (by decide)).trans P.hclassSize
    hclassStart := (rd.frame_arr "repairClassStart" (by decide)).trans P.hclassStart
    hord := (rd.frame_arr "ord" (by decide)).trans P.hord
    hoff := (rd.frame_arr "off" (by decide)).trans P.hoff
    htgt := (rd.frame_arr "tgt" (by decide)).trans P.htgt
    hgroupActive := (rd.frame_arr "activeB" (by decide)).trans P.hgroupActive
    hxsCard := P.hxsCard
    hxsRange := P.hxsRange
    hactiveCard := P.hactiveCard
    hslice := P.hslice
    hstartTable := P.hstartTable
    hclassEnd := P.hclassEnd
    hclassFibre := P.hclassFibre
    hbrange := P.hbrange
    hqle := P.hqle
    hlabel := P.hlabel
    hWrange := P.hWrange
    hWbase := P.hWbase
    hn1B := P.hn1B
    htargetCapB := P.htargetCapB
    hbuffer := P.hbuffer
    hsB := P.hsB
    htB := P.htB
    hmB := by
      have hcard : X.card ≤ n := by
        calc
          X.card ≤ (Finset.range n).card := Finset.card_le_card hXrange
          _ = n := by simp
      have := P.hn1B
      omega
    hpowB := hpowB
    hthreeB := P.hthreeB
  }
  have hcapAfter : Rafter.σ.vars "repairRetryCap" = cap := by
    change σd.vars "repairRetryCap" = cap
    rw [rd.frame_var "repairRetryCap" (by decide)]
    exact hcap
  obtain ⟨σ', attempts, totalUsed, rr, hattempts, hused,
    hinp, hn', hqpow, htrial, hrow, hdesired, hout⟩ :=
    localRepairRetriesSource_run Rafter hcapAfter hcapB hbudget
  have hfarAfter : σd.vars "repairFarBound" = (2 * k) / 3 := by
    rw [rd.frame_var "repairFarBound" (by decide)]
    exact hfar
  have hcond : (Cond.lt (.var "repairFarBound") (.var "drawModulus")).evalB
      B σd = some true := by
    have hfb : σd.vars "repairFarBound" < B := by rw [hfarAfter]; exact hfarB
    have hmb : σd.vars "drawModulus" < B := by rw [hmod]; exact Rafter.hmB
    simpa [hfarAfter, hmod, hfarCase] using
      (evalB_condLt (evalB_var hfb) (evalB_var hmb))
  have hUpper : Rafter.scanUpper = P.scanUpper := rfl
  rw [hUpper] at rr
  have rite : Run B (.ite (.lt (.var "repairFarBound") (.var "drawModulus"))
      localRepairRetriesSource (.assign "repairRetryStatus" (.lit 1))) σd σ'
      (4 + (12 * Nat.clog 2 X.card + 24 +
        ((15 * Nat.clog 2 X.card + 30) * totalUsed +
          attempts * (79 * s + P.scanUpper + 50) + 14))) := by
    simpa [Cond.size, Expr.size] using (Run.ite_true hcond rr)
  refine ⟨σ', attempts, totalUsed, ?_, hattempts, hused,
    hinp, hn', ?_, htrial, hrow, hdesired, ?_, ?_, hout⟩
  · simpa [localRepairOneExceptionSource] using rd.seq rite
  · exact hqpow.trans (rd.frame_var "qpow" (by decide))
  · exact (rr.frame_arr "repairBMarks" (by decide)).trans hBmarks
  · exact (rr.frame_arr "repairRMarks" (by decide)).trans hRmarks

/-- The near branch also covers an empty symmetric difference. It runs the
domain builder, assigns completed status, and reads no random bits. -/
lemma localRepairOneException_run_near
    {B n s t bufferCap targetCap q b k : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {groupedB Wbase Wcurrent A X : Finset ℕ}
    {rep blist rlist : ℕ → ℕ}
    (P : PreDomainInput B n s t bufferCap targetCap q b
      G x groupedB Wbase Wcurrent)
    (hA : A ⊆ Finset.range n)
    (hrep : P.σ.arrs "repB" = arrOf n rep)
    (hactive : P.σ.arrs "activeA" = arrOf n (setFlag A))
    (hbmarks : P.σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hrmarks : P.σ.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hblist : P.σ.arrs "repairBList" = arrOf n blist)
    (hrlist : P.σ.arrs "repairRList" = arrOf n rlist)
    (hr : rep b < n)
    (hXeq : X = ((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G (rep b) ∩ A)))
    (hfar : P.σ.vars "repairFarBound" = (2 * k) / 3)
    (hfarB : (2 * k) / 3 < B)
    (hnearCase : X.card ≤ (2 * k) / 3) :
    ∃ σ', Run B localRepairOneExceptionSource P.σ σ'
        ((54 * ((offset x (b + 1) - offset x b) +
            (offset x (rep b + 1) - offset x (rep b))) +
            36 * (((numericNeighborhood G b ∩ A).card) +
              ((numericNeighborhood G (rep b) ∩ A).card)) + 73) + 6) ∧
      σ'.inp = P.bits.map Bool.toNat ++ P.rest ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = P.σ.vars "qpow" ∧
      σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent) ∧
      σ'.vars "repairRetryStatus" = 1 ∧
      σ'.arrs "trialActive" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairRMarks" = arrOf n (fun _ => 0) := by
  obtain ⟨σd, domain', rd, hdomain, hmod, henum, hXrange,
    hBmarks, hRmarks, hsample, hn, hinpD⟩ :=
    preDomain_run P hA hrep hactive hbmarks hrmarks hblist hrlist hr hXeq
  have hfarAfter : σd.vars "repairFarBound" = (2 * k) / 3 := by
    rw [rd.frame_var "repairFarBound" (by decide)]
    exact hfar
  have hcond : (Cond.lt (.var "repairFarBound") (.var "drawModulus")).evalB
      B σd = some false := by
    have hfb : σd.vars "repairFarBound" < B := by rw [hfarAfter]; exact hfarB
    have hmb : σd.vars "drawModulus" < B := by
      rw [hmod]
      have hcard : X.card ≤ n := by
        calc
          X.card ≤ (Finset.range n).card := Finset.card_le_card hXrange
          _ = n := by simp
      have := P.hn1B
      omega
    have hnot : ¬ (2 * k) / 3 < X.card := by omega
    simpa [hfarAfter, hmod, hnot] using
      (evalB_condLt (evalB_var hfb) (evalB_var hmb))
  let σ' := σd.setVar "repairRetryStatus" 1
  have rassign : Run B (.assign "repairRetryStatus" (.lit 1)) σd σ' 2 := by
    simpa [σ'] using (Run.assign (x := "repairRetryStatus")
      (evalB_lit (by have := P.hthreeB; omega : 1 < B)))
  have rite : Run B (.ite (.lt (.var "repairFarBound") (.var "drawModulus"))
      localRepairRetriesSource (.assign "repairRetryStatus" (.lit 1)))
      σd σ' 6 := by
    simpa [Cond.size, Expr.size] using
      (Run.ite_false (c := localRepairRetriesSource) hcond rassign)
  refine ⟨σ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [localRepairOneExceptionSource] using rd.seq rite
  · simpa [σ', hinpD] using P.hinput
  · simpa [σ'] using hn
  · simpa [σ'] using (rd.frame_var "qpow" (by decide))
  · simpa [σ'] using hsample
  · simp [σ']
  · simpa [σ'] using (rd.frame_arr "trialActive" (by decide)).trans P.htrialZero
  · simpa [σ'] using (rd.frame_arr "trialRowMarks" (by decide)).trans P.hrowZero
  · simpa [σ'] using (rd.frame_arr "trialDesiredMarks" (by decide)).trans P.hdesiredZero
  · simpa [σ'] using hBmarks
  · simpa [σ'] using hRmarks

/-- A single entry theorem for the complete one-exception command. Status 1
means either a near domain was skipped unchanged or a far trial passed the
actual class scan. Status 2 is capped random-draw failure; status 3 is retry
exhaustion. Both leave the current sample unchanged. -/
lemma localRepairOneException_run
    {B n s t bufferCap targetCap q b cap k : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {groupedB Wbase Wcurrent A X : Finset ℕ}
    {rep blist rlist : ℕ → ℕ}
    (P : PreDomainInput B n s t bufferCap targetCap q b
      G x groupedB Wbase Wcurrent)
    (hA : A ⊆ Finset.range n)
    (hrep : P.σ.arrs "repB" = arrOf n rep)
    (hactive : P.σ.arrs "activeA" = arrOf n (setFlag A))
    (hbmarks : P.σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hrmarks : P.σ.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hblist : P.σ.arrs "repairBList" = arrOf n blist)
    (hrlist : P.σ.arrs "repairRList" = arrOf n rlist)
    (hr : rep b < n)
    (hXeq : X = ((numericNeighborhood G b ∩ A) ∆
      (numericNeighborhood G (rep b) ∩ A)))
    (hfar : P.σ.vars "repairFarBound" = (2 * k) / 3)
    (hfarB : (2 * k) / 3 < B)
    (hcap : P.σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hpowB : 2 ^ Nat.clog 2 X.card < B)
    (hbudget : cap * (s * t * Nat.clog 2 X.card) ≤ P.bits.length) :
    ∃ (σ' : Env) (attempts totalUsed : ℕ),
      Run B localRepairOneExceptionSource P.σ σ'
        ((54 * ((offset x (b + 1) - offset x b) +
            (offset x (rep b + 1) - offset x (rep b))) +
            36 * (((numericNeighborhood G b ∩ A).card) +
              ((numericNeighborhood G (rep b) ∩ A).card)) + 73) +
          (4 + (12 * Nat.clog 2 X.card + 24 +
            ((15 * Nat.clog 2 X.card + 30) * totalUsed +
              attempts * (79 * s + P.scanUpper + 50) + 14)))) ∧
      attempts ≤ cap ∧ totalUsed ≤ attempts * (s * t) ∧
      σ'.inp = (P.bits.drop (totalUsed * Nat.clog 2 X.card)).map Bool.toNat ++ P.rest ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = P.σ.vars "qpow" ∧
      σ'.arrs "trialActive" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "trialDesiredMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairRMarks" = arrOf n (fun _ => 0) ∧
      ((σ'.vars "repairRetryStatus" = 1 ∧
          ((X.card ≤ (2 * k) / 3 ∧
              σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) ∨
            ∃ D : List ℕ, D.length = s ∧ (∀ v ∈ D, v ∈ X) ∧
              localTrialIsolates (numericNeighborhood G) groupedB Wbase b D ∧
              σ'.arrs "sampleFlags" = arrOf n (setFlag (Wcurrent ∪ D.toFinset)))) ∨
        (σ'.vars "repairRetryStatus" = 2 ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent)) ∨
        (σ'.vars "repairRetryStatus" = 3 ∧ attempts = cap ∧
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) := by
  by_cases hfarCase : (2 * k) / 3 < X.card
  · obtain ⟨σ', attempts, totalUsed, r, ha, hu, hinp, hn, hq,
      htrial, hrow, hdesired, hBmarks, hRmarks, hout⟩ :=
      localRepairOneException_run_far P hA hrep hactive hbmarks hrmarks
        hblist hrlist hr hXeq hfar hfarB hfarCase hcap hcapB hpowB hbudget
    refine ⟨σ', attempts, totalUsed, r, ha, hu, hinp, hn, hq,
      htrial, hrow, hdesired, hBmarks, hRmarks, ?_⟩
    rcases hout with hsuccess | hfailure | hexhaust
    · left
      refine ⟨hsuccess.1, Or.inr ?_⟩
      exact hsuccess.2
    · exact Or.inr (Or.inl hfailure)
    · exact Or.inr (Or.inr hexhaust)
  · have hnearCase : X.card ≤ (2 * k) / 3 := Nat.le_of_not_gt hfarCase
    obtain ⟨σ', r, hinp, hn, hq, hsample, hstatus,
      htrial, hrow, hdesired, hBmarks, hRmarks⟩ :=
      localRepairOneException_run_near P hA hrep hactive hbmarks hrmarks
        hblist hrlist hr hXeq hfar hfarB hnearCase
    refine ⟨σ', 0, 0, ?_, by omega, by simp, ?_, hn, hq,
      htrial, hrow, hdesired, hBmarks, hRmarks, ?_⟩
    · apply r.mono
      simp only [zero_mul, Nat.zero_mul, Nat.add_zero]
      omega
    · simpa using hinp
    · exact Or.inl ⟨hstatus, Or.inl ⟨hnearCase, hsample⟩⟩

end
end Lax457868Proofs.LocalRepairRetriesSource
