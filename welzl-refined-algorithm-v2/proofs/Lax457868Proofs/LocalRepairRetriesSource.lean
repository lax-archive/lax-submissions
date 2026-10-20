import Lax457868Proofs.LocalRepairSource
import Lax457868Proofs.LocalFlatLaw
import Lax457868Proofs.RepairFilterSource
import Lax457868Proofs.SourceTapePrefix
import Mathlib.Tactic

/-! One fixed bounded retry loop for the concrete local repair trial. -/

namespace Lax457868Proofs.LocalRepairRetriesSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.LocalRepairSource
open Lax457868Proofs.LocalFlatLaw
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

/-- The actual ordered retry prefix ends in a capped selector failure.
Earlier trials are complete and rejected; the final failed draw is kept with
its exact unread tail. -/
inductive FlatSelectorFailed (m : ℕ) (hm : 0 < m) (t s : ℕ)
    (bad : Finset (List ℕ)) : ℕ → List Bool → Prop
  | final {bits : List Bool}
      (blockTape : Fin (s * t) → (Fin (Nat.clog 2 m) → Bool))
      (tail : List Bool) (values : List (Fin m)) (used : ℕ)
      (hbits : bits = (List.ofFn blockTape).flatMap List.ofFn ++ tail)
      (hdraw : SequentialDraws.DrawTrace m hm t s
        (List.ofFn blockTape) values used true) :
      FlatSelectorFailed m hm t s bad 1 bits
  | rejected {bits : List Bool} {k : ℕ}
      (blockTape : Fin (s * t) → (Fin (Nat.clog 2 m) → Bool))
      (tail : List Bool) (values : List (Fin m)) (used : ℕ)
      (hbits : bits = (List.ofFn blockTape).flatMap List.ofFn ++ tail)
      (hdraw : SequentialDraws.DrawTrace m hm t s
        (List.ofFn blockTape) values used false)
      (hbad : values.map Fin.val ∈ bad)
      (hnext : FlatSelectorFailed m hm t s bad k
        (bits.drop (used * Nat.clog 2 m))) :
      FlatSelectorFailed m hm t s bad (k + 1) bits

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
lemma localRepairWhile_run_trace
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
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) ∧
      (∃ rejected : ℕ,
        rejected ≤ attempts ∧ attempts ≤ rejected + 1 ∧
        FlatRejectedTrials m t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) rejected R.bits) ∧
      (∃ accepted : ℕ,
        FlatRetryExecution m R.hpositive t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits totalUsed accepted) ∧
      σ'.vars "repairRetriesLeft" + attempts = fuel ∧
      (σ'.vars "repairRetryStatus" = 3 →
        FlatRejectedTrials m t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits) ∧
      (σ'.vars "repairRetryStatus" = 2 →
        FlatSelectorFailed m R.hpositive t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits) := by
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
    · constructor
      · right; right
        simp [σ', R.hsample]
      · constructor
        · exact ⟨0, by omega, by omega, FlatRejectedTrials.done R.bits⟩
        · constructor
          · exact ⟨0, FlatRetryExecution.done R.bits⟩
          · constructor
            · simp [σ', hleft]
            · constructor
              · intro _
                exact FlatRejectedTrials.done R.bits
              · intro hstatus2
                simp [σ'] at hstatus2
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
    obtain ⟨values, used, failed, σa, rtrial, htraceWitness, hused, hcomplete,
      hinp, hX, htrial, hrow, hdesired, hn, hqpow,
      hfail, hstatusLe, hsuccess⟩ :=
      localRepairTrial_run_bits_trace R hL hv hbudgetOne
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
      · constructor
        · right; left
          exact ⟨hstatus2, by rw [hflagsB]; exact hflagsA⟩
        · constructor
          · exact ⟨0, by omega, by omega, FlatRejectedTrials.done R.bits⟩
          · constructor
            · obtain ⟨blockTape, tail, hsplit, hdraw⟩ := htraceWitness
              exact ⟨values.length,
                FlatRetryExecution.final blockTape tail values used failed
                  (by simpa [ClassRepresentativeTrace.tapeBits] using hsplit)
                  hdraw⟩
            · constructor
              · simp [σb, hleftA]
              · constructor
                · intro hstatus3
                  omega
                · intro _
                  obtain ⟨blockTape, tail, hsplit, hdraw⟩ := htraceWitness
                  exact FlatSelectorFailed.final blockTape tail values used
                    (by simpa [ClassRepresentativeTrace.tapeBits] using hsplit)
                    (by simpa [hfailed] using hdraw)
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
          hinp', hn', hqpow', htrial', hrow', hdesired', hout', htrace',
          hfull', hcount', hexhaustTrace', hselectorTrace'⟩ :=
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
        obtain ⟨blockTape, tail, hsplit, hdraw⟩ := htraceWitness
        have hdrawFalse : SequentialDraws.DrawTrace m R.hpositive t s
            (List.ofFn blockTape) values used false := by
          simpa [hfalse] using hdraw
        have hbudgetFlat :
            ClassRepresentativeTrace.bitBudget (fun _ => m) t 0 s ≤
              ((List.ofFn blockTape).flatMap List.ofFn ++ tail).length := by
          rw [← ClassRepresentativeTrace.tapeBits, ← hsplit,
            LocalFlatLaw.local_bitBudget]
          simpa [L] using hbudgetOne
        obtain ⟨stopAttempts, hflatRaw, hconsumed⟩ :=
          LocalFlatLaw.drawTrace_success_flat_used m R.hpositive t s used
            (List.ofFn blockTape) values tail hdrawFalse hbudgetFlat
        have hflat : FlatTraceLaw.FlatClassSuccess (fun _ => m) t
            (fun _ => 0) 0 s R.bits (values.map Fin.val) stopAttempts := by
          have hbitsEq : (List.ofFn blockTape).flatMap List.ofFn ++ tail =
              R.bits := by
            simpa [ClassRepresentativeTrace.tapeBits] using hsplit.symm
          rw [hbitsEq] at hflatRaw
          exact hflatRaw
        have hvalid : values.map Fin.val ∈
            FlatTraceLaw.outputVectors (fun _ => m) (fun _ => 0) 0 s :=
          FlatTraceLaw.ValidOutput.mem_outputVectors (fun _ => m)
            (fun _ => 0)
            (FlatTraceLaw.ValidPath.validOutput (fun _ => m) t
              (fun _ => 0)
              (FlatTraceLaw.FlatClassSuccess.validPath (fun _ => m) t
                (fun _ => 0) hflat))
        have hnot : ¬ localTrialIsolates (numericNeighborhood G)
            groupedB Wbase b D := by
          intro hiso
          exact (by omega : σa.vars "repairRetryStatus" ≠ 1)
            ((hsuccess hfalse).1.mpr hiso)
        have hbad : values.map Fin.val ∈ localBadOutputs m s R.domain
            (numericNeighborhood G) groupedB Wbase b := by
          simp only [localBadOutputs, Finset.mem_filter]
          constructor
          · exact hvalid
          · simpa [D, List.map_map, Function.comp_def] using hnot
        refine ⟨σ', attempts' + 1, used + totalUsed', ?_, by omega,
          htotal, ?_, hn', hqpowFinal, htrial', hrow', hdesired', ?_⟩
        · apply (runWhileTrue hguard rbody rrec').mono
          dsimp [Cond.size, Expr.size]
          change 4 + (K + 8) + (C * totalUsed' + attempts' * A + 14) ≤
            C * (used + totalUsed') + (attempts' + 1) * A + 14
          dsimp [K, A]
          nlinarith [hcharge]
        · simpa [Nat.clog, L] using hinputFinal
        · constructor
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
          · constructor
            · obtain ⟨rejected', hrejectLe, hattemptLe, hnextRaw⟩ := htrace'
              have hnext : FlatRejectedTrials m t s
                (localBadOutputs m s R.domain (numericNeighborhood G)
                  groupedB Wbase b) rejected'
                (R.bits.drop (FlatTraceLaw.consumedBits (fun _ => m) 0
                  stopAttempts)) := by
                change FlatRejectedTrials m t s
                  (localBadOutputs m s R.domain (numericNeighborhood G)
                    groupedB Wbase b) rejected'
                  (R.bits.drop (used * L)) at hnextRaw
                simpa [L, hconsumed] using hnextRaw
              exact ⟨rejected' + 1, by omega, by omega,
                FlatRejectedTrials.step (values.map Fin.val) stopAttempts
                  hbad hflat hnext⟩
            · constructor
              · obtain ⟨accepted', hnext⟩ := hfull'
                have hnext' : FlatRetryExecution m R.hpositive t s
                    (localBadOutputs m s R.domain (numericNeighborhood G)
                      groupedB Wbase b) attempts'
                    (R.bits.drop (used * L)) totalUsed' accepted' := by
                  change FlatRetryExecution m R.hpositive t s
                    (localBadOutputs m s R.domain (numericNeighborhood G)
                      groupedB Wbase b) attempts'
                    (R.bits.drop (used * L)) totalUsed' accepted' at hnext
                  exact hnext
                exact ⟨s + accepted',
                  FlatRetryExecution.rejected blockTape tail values used
                    (by simpa [ClassRepresentativeTrace.tapeBits] using hsplit)
                    hdrawFalse hbad hnext'⟩
              · constructor
                · omega
                · constructor
                  · intro hstatus3
                    have hnextRaw := hexhaustTrace' hstatus3
                    change FlatRejectedTrials m t s
                      (localBadOutputs m s R.domain
                        (numericNeighborhood G) groupedB Wbase b)
                      attempts' (R.bits.drop (used * L)) at hnextRaw
                    have hnext : FlatRejectedTrials m t s
                        (localBadOutputs m s R.domain
                          (numericNeighborhood G) groupedB Wbase b)
                        attempts' (R.bits.drop
                          (FlatTraceLaw.consumedBits (fun _ => m) 0
                            stopAttempts)) := by
                      simpa [L, hconsumed] using hnextRaw
                    exact FlatRejectedTrials.step
                      (values.map Fin.val) stopAttempts hbad hflat hnext
                  · intro hstatus2
                    have hnextRaw := hselectorTrace' hstatus2
                    change FlatSelectorFailed m R.hpositive t s
                      (localBadOutputs m s R.domain
                        (numericNeighborhood G) groupedB Wbase b)
                      attempts' (R.bits.drop (used * L)) at hnextRaw
                    exact FlatSelectorFailed.rejected blockTape tail values used
                      (by simpa [ClassRepresentativeTrace.tapeBits] using hsplit)
                      hdrawFalse hbad hnextRaw
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
        · constructor
          · left
            refine ⟨hstatus1B, D, hlen, ?_, (hiff.mp hstatus1), ?_⟩
            · simpa [D] using hX
            · rw [hflagsB]
              exact hflagsA
          · constructor
            · exact ⟨0, by omega, by omega, FlatRejectedTrials.done R.bits⟩
            · constructor
              · obtain ⟨blockTape, tail, hsplit, hdraw⟩ := htraceWitness
                exact ⟨values.length,
                  FlatRetryExecution.final blockTape tail values used failed
                    (by simpa [ClassRepresentativeTrace.tapeBits] using hsplit)
                    hdraw⟩
              · constructor
                · simp [σb, hleftA]
                · constructor
                  · intro hstatus3
                    omega
                  · intro hstatus2
                    omega


/-- Preserve the original while-run interface for existing callers. -/
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
  obtain ⟨σ', attempts, totalUsed, hrun, hattempts, hused,
    hinp, hn, hq, htrial, hrow, hdesired, hout, _⟩ :=
    localRepairWhile_run_trace fuel R hstatus hleft hL hv hfuelB hbudget
  exact ⟨σ', attempts, totalUsed, hrun, hattempts, hused,
    hinp, hn, hq, htrial, hrow, hdesired, hout⟩

/-- The full one-exception source initializes its retry register, computes the
draw width once, and runs the bounded while-command. The returned bit suffix
is exact; the charge includes logarithm setup once and only used draw bits
thereafter. -/
lemma localRepairRetriesSource_run_trace_failure
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
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) ∧
      (∃ rejected : ℕ,
        rejected ≤ attempts ∧ attempts ≤ rejected + 1 ∧
        FlatRejectedTrials m t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) rejected R.bits) ∧
      (∃ accepted : ℕ,
        FlatRetryExecution m R.hpositive t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits totalUsed accepted) ∧
      σ'.vars "repairRetriesLeft" + attempts = cap ∧
      (σ'.vars "repairRetryStatus" = 3 →
        FlatRejectedTrials m t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits) ∧
      (σ'.vars "repairRetryStatus" = 2 →
        FlatSelectorFailed m R.hpositive t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits) := by
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
    hinp, hn, hq, htrial, hrow, hdesired, hout, htrace⟩ :=
    localRepairWhile_run_trace cap Rready hstatus4 hleft4 hL4 hv4 hcapB hbudget
  refine ⟨σ', attempts, totalUsed, ?_, hattempts, hused, hinp,
    hn, ?_, htrial, hrow, hdesired, hout, ?_⟩
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
  · simpa [Rready] using htrace

lemma localRepairRetriesSource_run_trace_exhaust
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
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) ∧
      (∃ rejected : ℕ,
        rejected ≤ attempts ∧ attempts ≤ rejected + 1 ∧
        FlatRejectedTrials m t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) rejected R.bits) ∧
      (∃ accepted : ℕ,
        FlatRetryExecution m R.hpositive t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits totalUsed accepted) ∧
      σ'.vars "repairRetriesLeft" + attempts = cap ∧
      (σ'.vars "repairRetryStatus" = 3 →
        FlatRejectedTrials m t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits) := by
  obtain ⟨σ', attempts, totalUsed, hrun, ha, hu, hinp,
    hn, hq, htrial, hrow, hdesired, hout, hreject, hfull,
    hcount, hexhaust, _hselector⟩ :=
    localRepairRetriesSource_run_trace_failure R hcap hcapB hbudget
  exact ⟨σ', attempts, totalUsed, hrun, ha, hu, hinp,
    hn, hq, htrial, hrow, hdesired, hout, hreject, hfull,
    hcount, hexhaust⟩

lemma localRepairRetriesSource_run_trace
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
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) ∧
      (∃ rejected : ℕ,
        rejected ≤ attempts ∧ attempts ≤ rejected + 1 ∧
        FlatRejectedTrials m t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) rejected R.bits) ∧
      (∃ accepted : ℕ,
        FlatRetryExecution m R.hpositive t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits totalUsed accepted) ∧
      σ'.vars "repairRetriesLeft" + attempts = cap := by
  obtain ⟨σ', attempts, totalUsed, hrun, ha, hu, hinp,
    hn, hq, htrial, hrow, hdesired, hout, hreject, hfull,
    hcount, _hexhaust⟩ :=
    localRepairRetriesSource_run_trace_exhaust R hcap hcapB hbudget
  exact ⟨σ', attempts, totalUsed, hrun, ha, hu, hinp,
    hn, hq, htrial, hrow, hdesired, hout, hreject, hfull, hcount⟩

/-- Preserve the original source-run interface for existing callers. -/
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
  obtain ⟨σ', attempts, totalUsed, hrun, hattempts, hused, hinp,
    hn, hq, htrial, hrow, hdesired, hout, _, _⟩ :=
    localRepairRetriesSource_run_trace R hcap hcapB hbudget
  exact ⟨σ', attempts, totalUsed, hrun, hattempts, hused, hinp,
    hn, hq, htrial, hrow, hdesired, hout⟩

/-- The exact number of input words consumed by a deterministic source run
is stable when only unread input and the environment's input field change. -/
lemma run_consumption_causal
    {B K₁ K₂ u₁ u₂ : ℕ} {c : Com}
    {σ₁ σ₂ τ₁ τ₂ : Env}
    {bits₁ bits₂ rest₁ rest₂ : List ℕ}
    (hvars : σ₁.vars = σ₂.vars)
    (harrs : σ₁.arrs = σ₂.arrs)
    (hout : σ₁.out = σ₂.out)
    (hstart₁ : σ₁.inp = bits₁ ++ rest₁)
    (hstart₂ : σ₂.inp = bits₂ ++ rest₂)
    (hend₁ : τ₁.inp = bits₁.drop u₁ ++ rest₁)
    (hend₂ : τ₂.inp = bits₂.drop u₂ ++ rest₂)
    (hu₁ : u₁ ≤ bits₁.length)
    (hu₁' : u₁ ≤ bits₂.length)
    (hu₂ : u₂ ≤ bits₂.length)
    (hprefix : bits₁.take u₁ = bits₂.take u₁)
    (hrun₁ : Run B c σ₁ τ₁ K₁)
    (hrun₂ : Run B c σ₂ τ₂ K₂) :
    u₁ = u₂ := by
  obtain ⟨k₁, _, hbig₁⟩ := hrun₁
  obtain ⟨pre, hin, _, hreplay⟩ :=
    SourceTapePrefix.consumed_prefix hbig₁
  have hpreLen : pre.length = u₁ := by
    have hlen := congrArg List.length hin
    rw [hstart₁, hend₁] at hlen
    simp only [List.length_append, List.length_drop] at hlen
    omega
  have hpre : pre = bits₁.take u₁ := by
    have htake : σ₁.inp.take pre.length = pre := by
      rw [hin]
      simp
    rw [hstart₁, hpreLen,
      List.take_append_of_le_length hu₁] at htake
    exact htake.symm
  have hinput₂ : σ₂.inp = pre ++ (bits₂.drop u₁ ++ rest₂) := by
    calc
      σ₂.inp = bits₂ ++ rest₂ := hstart₂
      _ = bits₂.take u₁ ++ (bits₂.drop u₁ ++ rest₂) := by
        simp [← List.append_assoc, List.take_append_drop]
      _ = pre ++ (bits₂.drop u₁ ++ rest₂) := by rw [hpre, hprefix]
  have hstate : {σ₁ with inp := pre ++ (bits₂.drop u₁ ++ rest₂)} = σ₂ := by
    rw [← hinput₂]
    cases σ₁
    cases σ₂
    simp_all
  have hreplay' : BigStepB B c σ₂
      {τ₁ with inp := bits₂.drop u₁ ++ rest₂} k₁ := by
    rw [← hstate]
    exact hreplay _
  obtain ⟨k₂, _, hbig₂⟩ := hrun₂
  obtain ⟨heq, _⟩ := BigStep.unique hreplay'.bigStep hbig₂.bigStep
  have hinpEq := congrArg Env.inp heq
  simp only [hend₂] at hinpEq
  have hlen := congrArg List.length hinpEq
  simp only [List.length_append, List.length_drop] at hlen
  omega

/-- Every actual trial beyond position `j` certifies `j` consecutive
completed, rejected stopped-prefix trials on the same original fair-bit tape. -/
lemma localRepairRetriesSource_run_tail
    {B n m domainCap s t bufferCap targetCap q b cap Nbits : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    (tape : FlatTraceLaw.FlatTape Nbits)
    (hbits : R.bits = FlatTraceLaw.flatBits tape)
    (hcap : R.σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ Nbits) :
    ∃ (σ' : Env) (attempts totalUsed : ℕ),
      Run B localRepairRetriesSource R.σ σ'
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * totalUsed +
            attempts * (79 * s + R.scanUpper + 50) + 14)) ∧
      attempts ≤ cap ∧ totalUsed ≤ attempts * (s * t) ∧
      (∀ j < attempts,
        tape ∈ retryRejectedFiber m t s j Nbits
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b)) ∧
      σ'.inp = (R.bits.drop (totalUsed * Nat.clog 2 m)).map Bool.toNat ++
        R.rest ∧
      (∃ accepted : ℕ,
        FlatRetryExecution m R.hpositive t s
          (localBadOutputs m s R.domain (numericNeighborhood G)
            groupedB Wbase b) attempts R.bits totalUsed accepted) ∧
      σ'.vars "repairRetriesLeft" + attempts = cap := by
  have hbudgetBits : cap * (s * t * Nat.clog 2 m) ≤ R.bits.length := by
    rw [hbits, FlatTraceLaw.flatBits_length]
    exact hbudget
  obtain ⟨σ', attempts, totalUsed, hrun, hattempts, hused,
    hinp, _, _, _, _, _, _, htrace, hfull, hcount⟩ :=
    localRepairRetriesSource_run_trace R hcap hcapB hbudgetBits
  obtain ⟨rejected, hrejectLe, hattemptLe, hflat⟩ := htrace
  refine ⟨σ', attempts, totalUsed, hrun, hattempts, hused, ?_, hinp,
    hfull, hcount⟩
  intro j hj
  have hjle : j ≤ rejected := by omega
  have hprefix := FlatRejectedTrials.prefix m t s
    (localBadOutputs m s R.domain (numericNeighborhood G)
      groupedB Wbase b) hflat j hjle
  rw [hbits] at hprefix
  simpa [retryRejectedFiber] using hprefix

/-- The actual bounded local-retry source has mean attempt count at most two
on a uniform flat-bit input family. Each selected witness is a real source
`Run` with the exact unread suffix and its original runtime upper bound. -/
lemma localRepairRetriesSource_mean_attempts_le_two
    {B n m domainCap s t bufferCap targetCap q b cap Nbits : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape Nbits →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ Nbits)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (Lax457868Proofs.SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ attempts : FlatTraceLaw.FlatTape Nbits → ℕ,
      (∀ tape, attempts tape ≤ cap ∧
        ∃ (σ' : Env) (totalUsed : ℕ),
          Run B localRepairRetriesSource (R tape).σ σ'
            (12 * Nat.clog 2 m + 24 +
              ((15 * Nat.clog 2 m + 30) * totalUsed +
                attempts tape * (79 * s + (R tape).scanUpper + 50) + 14)) ∧
          totalUsed ≤ attempts tape * (s * t)) ∧
      (∑ tape : FlatTraceLaw.FlatTape Nbits, (attempts tape : ℚ)) ≤
        2 * (2 ^ Nbits : ℚ) := by
  classical
  let bad := localBadOutputs m s domain (numericNeighborhood G)
    groupedB Wbase b
  have hvalid : bad ⊆ FlatTraceLaw.outputVectors (fun _ => m)
      (fun _ => 0) 0 s := by
    intro output houtput
    exact (Finset.mem_filter.mp houtput).1
  have hhalfBad : 2 * bad.card ≤
      FlatTraceLaw.outputCount (fun _ => m) 0 s := by
    rw [show bad = localBadOutputs m s domain (numericNeighborhood G)
      groupedB Wbase b from rfl,
      LocalFlatLaw.card_localBadOutputs_eq_failureSet m s domain X henum,
      LocalFlatLaw.local_outputCount]
    have hmX := EnumeratedDraws.prefixEnumerates_card m domain X henum
    simpa [hmX] using hhalf
  have hbudgetFlat : cap * ClassRepresentativeTrace.bitBudget
      (fun _ => m) t 0 s ≤ Nbits := by
    rw [LocalFlatLaw.local_bitBudget]
    exact hbudget
  have hex : ∀ tape : FlatTraceLaw.FlatTape Nbits,
      ∃ attempts : ℕ, attempts ≤ cap ∧
        (∀ j < attempts, tape ∈ retryRejectedFiber m t s j Nbits bad) ∧
        ∃ (σ' : Env) (totalUsed : ℕ),
          Run B localRepairRetriesSource (R tape).σ σ'
            (12 * Nat.clog 2 m + 24 +
              ((15 * Nat.clog 2 m + 30) * totalUsed +
                attempts * (79 * s + (R tape).scanUpper + 50) + 14)) ∧
          totalUsed ≤ attempts * (s * t) := by
    intro tape
    obtain ⟨σ', attempts, totalUsed, hrun, hattempts, hused, htail,
      _, _, _⟩ :=
      localRepairRetriesSource_run_tail (R tape) tape (hbits tape)
        (hcap tape) hcapB hbudget
    refine ⟨attempts, hattempts, ?_, σ', totalUsed, hrun, hused⟩
    intro j hj
    simpa [bad, hdomain tape] using htail j hj
  choose attempts hchosen using hex
  refine ⟨attempts, ?_, ?_⟩
  · intro tape
    exact ⟨(hchosen tape).1, (hchosen tape).2.2⟩
  · apply LocalFlatLaw.sourceAttempts_sum_le_two m t s cap Nbits bad
      hvalid hhalfBad hbudgetFlat attempts
    · intro tape
      exact (hchosen tape).1
    · intro tape j hj
      exact (hchosen tape).2.1 j hj

/-- One coherent choice of actual retry runs retains the whole stopped draw
trace, exact unread bit suffix, and the same two-trial mean bound. -/
lemma localRepairRetriesSource_mean_full_trace_le_two
    {B n m domainCap s t bufferCap targetCap q b cap Nbits : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape Nbits →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ Nbits)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ (attempts used accepted : FlatTraceLaw.FlatTape Nbits → ℕ)
      (finalState : FlatTraceLaw.FlatTape Nbits → Env),
      (∀ tape,
        Run B localRepairRetriesSource (R tape).σ (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + (R tape).scanUpper + 50) + 14)) ∧
        attempts tape ≤ cap ∧ used tape ≤ attempts tape * (s * t) ∧
        (finalState tape).inp =
          ((R tape).bits.drop (used tape * Nat.clog 2 m)).map Bool.toNat ++
            (R tape).rest ∧
        FlatRetryExecution m (R tape).hpositive t s
          (localBadOutputs m s domain (numericNeighborhood G)
            groupedB Wbase b) (attempts tape) (R tape).bits
            (used tape) (accepted tape) ∧
        (finalState tape).vars "repairRetriesLeft" + attempts tape = cap) ∧
      (∑ tape : FlatTraceLaw.FlatTape Nbits,
        (attempts tape : ℚ)) ≤ 2 * (2 ^ Nbits : ℚ) := by
  classical
  let bad := localBadOutputs m s domain (numericNeighborhood G)
    groupedB Wbase b
  have hvalid : bad ⊆ FlatTraceLaw.outputVectors (fun _ => m)
      (fun _ => 0) 0 s := by
    intro output houtput
    exact (Finset.mem_filter.mp houtput).1
  have hhalfBad : 2 * bad.card ≤
      FlatTraceLaw.outputCount (fun _ => m) 0 s := by
    rw [show bad = localBadOutputs m s domain (numericNeighborhood G)
      groupedB Wbase b from rfl,
      LocalFlatLaw.card_localBadOutputs_eq_failureSet m s domain X henum,
      LocalFlatLaw.local_outputCount]
    have hmX := EnumeratedDraws.prefixEnumerates_card m domain X henum
    simpa [hmX] using hhalf
  have hbudgetFlat : cap * ClassRepresentativeTrace.bitBudget
      (fun _ => m) t 0 s ≤ Nbits := by
    rw [LocalFlatLaw.local_bitBudget]
    exact hbudget
  have hex : ∀ tape : FlatTraceLaw.FlatTape Nbits,
      ∃ (attempts used accepted : ℕ) (finalState : Env),
        (∀ j < attempts, tape ∈ retryRejectedFiber m t s j Nbits bad) ∧
        Run B localRepairRetriesSource (R tape).σ finalState
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used +
              attempts * (79 * s + (R tape).scanUpper + 50) + 14)) ∧
        attempts ≤ cap ∧ used ≤ attempts * (s * t) ∧
        finalState.inp =
          ((R tape).bits.drop (used * Nat.clog 2 m)).map Bool.toNat ++
            (R tape).rest ∧
        FlatRetryExecution m (R tape).hpositive t s bad attempts
          (R tape).bits used accepted ∧
        finalState.vars "repairRetriesLeft" + attempts = cap := by
    intro tape
    obtain ⟨finalState, attempts, used, hrun, hattempts, hused,
      htail, hinp, ⟨accepted, hfull⟩, hcount⟩ :=
      localRepairRetriesSource_run_tail (R tape) tape (hbits tape)
        (hcap tape) hcapB hbudget
    refine ⟨attempts, used, accepted, finalState, ?_, hrun,
      hattempts, hused, hinp, ?_, hcount⟩
    · intro j hj
      simpa [bad, hdomain tape] using htail j hj
    · simpa [bad, hdomain tape] using hfull
  choose attempts used accepted finalState hchosen using hex
  refine ⟨attempts, used, accepted, finalState, ?_, ?_⟩
  · intro tape
    exact ⟨(hchosen tape).2.1, (hchosen tape).2.2⟩
  · have hmean := LocalFlatLaw.sourceAttempts_sum_le_two m t s cap
      Nbits bad hvalid hhalfBad hbudgetFlat attempts
      (fun tape => (hchosen tape).2.2.1)
      (fun tape j hj => (hchosen tape).1 j hj)
    exact hmean

/-- The actual block count is a stopping-time quantity: once its read bit
prefix is fixed, changing every unread input bit cannot alter it. -/
lemma localRepairRetriesSource_used_causal_bits
    {B n m domainCap s t bufferCap targetCap q b cap Nbits : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : FlatTraceLaw.FlatTape Nbits →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ Nbits)
    (hL : 0 < Nat.clog 2 m)
    (attempts used : FlatTraceLaw.FlatTape Nbits → ℕ)
    (finalState : FlatTraceLaw.FlatTape Nbits → Env)
    (hrun : ∀ tape, Run B localRepairRetriesSource
      (R tape).σ (finalState tape)
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + (R tape).scanUpper + 50) + 14)))
    (hattempts : ∀ tape, attempts tape ≤ cap)
    (hused : ∀ tape, used tape ≤ attempts tape * (s * t))
    (hinp : ∀ tape, (finalState tape).inp =
      ((R tape).bits.drop (used tape * Nat.clog 2 m)).map Bool.toNat ++
        (R tape).rest) :
    ∀ tape tape' k, k ≤ Nbits →
      (FlatTraceLaw.flatBits tape).take k =
        (FlatTraceLaw.flatBits tape').take k →
      used tape * Nat.clog 2 m ≤ k → used tape' = used tape := by
  intro tape tape' k hk hprefix hreach
  let L := Nat.clog 2 m
  have husedBits (a : FlatTraceLaw.FlatTape Nbits) :
      used a * L ≤ Nbits := by
    calc
      used a * L ≤ (attempts a * (s * t)) * L :=
        Nat.mul_le_mul_right L (hused a)
      _ ≤ (cap * (s * t)) * L :=
        Nat.mul_le_mul_right L
          (Nat.mul_le_mul_right (s * t) (hattempts a))
      _ = cap * (s * t * L) := by ring
      _ ≤ Nbits := hbudget
  have hprefixUsed :
      (FlatTraceLaw.flatBits tape).take (used tape * L) =
        (FlatTraceLaw.flatBits tape').take (used tape * L) := by
    have hr : used tape * L ≤ k := by simpa [L] using hreach
    have h := congrArg (List.take (used tape * L)) hprefix
    simpa only [List.take_take, min_eq_left hr] using h
  have hprefixWords :
      ((FlatTraceLaw.flatBits tape).map Bool.toNat).take (used tape * L) =
        ((FlatTraceLaw.flatBits tape').map Bool.toNat).take
          (used tape * L) := by
    simpa only [List.map_take] using
      congrArg (List.map Bool.toNat) hprefixUsed
  have hσ (a : FlatTraceLaw.FlatTape Nbits) :
      (R a).σ.inp = (FlatTraceLaw.flatBits a).map Bool.toNat ++
        (R a).rest := by
    rw [(R a).hinput, hbits a]
  have hτ (a : FlatTraceLaw.FlatTape Nbits) :
      (finalState a).inp =
        ((FlatTraceLaw.flatBits a).map Bool.toNat).drop (used a * L) ++
          (R a).rest := by
    rw [hinp a, hbits a]
    simp [L, List.map_drop]
  obtain ⟨hvars, harrs, hout⟩ := hstate tape tape'
  have hwords := run_consumption_causal hvars harrs hout
    (hσ tape) (hσ tape') (hτ tape) (hτ tape')
    (by simpa [L, FlatTraceLaw.flatBits_length] using husedBits tape)
    (by simpa [L, FlatTraceLaw.flatBits_length] using husedBits tape)
    (by simpa [L, FlatTraceLaw.flatBits_length] using husedBits tape')
    hprefixWords (hrun tape) (hrun tape')
  exact (Nat.eq_of_mul_eq_mul_right hL hwords).symm

/-- The exact stopped block count in a family of actual local retry Runs has
mean at most four blocks per requested local index. -/
lemma localRepairRetriesSource_mean_used_posWidth
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (hL : 0 < Nat.clog 2 m)
    (attempts used accepted :
      FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m) → ℕ)
    (finalState : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m) → Env)
    (hrun : ∀ tape, Run B localRepairRetriesSource
      (R tape).σ (finalState tape)
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + (R tape).scanUpper + 50) + 14)))
    (hattempts : ∀ tape, attempts tape ≤ cap)
    (hused : ∀ tape, used tape ≤ attempts tape * (s * t))
    (hinp : ∀ tape, (finalState tape).inp =
      ((R tape).bits.drop (used tape * Nat.clog 2 m)).map Bool.toNat ++
        (R tape).rest)
    (hfull : ∀ tape,
      LocalFlatLaw.FlatRetryExecution m (R tape).hpositive t s
        (LocalFlatLaw.localBadOutputs m s (R tape).domain
          (numericNeighborhood G) groupedB Wbase b)
        (attempts tape) (R tape).bits (used tape) (accepted tape))
    (hmean : (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m), (attempts tape : ℚ)) ≤
        2 * (2 ^ (Nblocks * Nat.clog 2 m) : ℚ)) :
    (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m),
      used tape) ≤ 4 * s * 2 ^ (Nblocks * Nat.clog 2 m) := by
  classical
  let L := Nat.clog 2 m
  let E := LocalFlatLaw.blockTapeBitsEquiv Nblocks L
  let attemptsB : (Fin Nblocks → Fin L → Bool) → ℕ :=
    fun tape => attempts (E tape)
  let usedB : (Fin Nblocks → Fin L → Bool) → ℕ :=
    fun tape => used (E tape)
  have hbudget : cap * (s * t * L) ≤ Nblocks * L := by
    have h := Nat.mul_le_mul_right L hblocks
    nlinarith
  have hbound (tape : Fin Nblocks → Fin L → Bool) :
      usedB tape ≤ Nblocks := by
    dsimp [usedB]
    exact (hused (E tape)).trans
      ((Nat.mul_le_mul_right (s * t) (hattempts (E tape))).trans
        hblocks)
  have hcausal (tape tape' : Fin Nblocks → Fin L → Bool) (k : ℕ)
      (hk : k ≤ Nblocks)
      (hpre : (List.ofFn tape).take k = (List.ofFn tape').take k)
      (hread : usedB tape ≤ k) : usedB tape' = usedB tape := by
    have hpreBits : (FlatTraceLaw.flatBits (E tape)).take (k * L) =
        (FlatTraceLaw.flatBits (E tape')).take (k * L) := by
      rw [LocalFlatLaw.flatBits_blockTapeBitsEquiv,
        LocalFlatLaw.flatBits_blockTapeBitsEquiv]
      change ((List.ofFn tape).flatMap List.ofFn).take (k * L) =
        ((List.ofFn tape').flatMap List.ofFn).take (k * L)
      rw [← LocalFlatLaw.flatMap_take_blocks,
        ← LocalFlatLaw.flatMap_take_blocks, hpre]
    exact localRepairRetriesSource_used_causal_bits R hbits hstate
      hbudget hL attempts used finalState hrun hattempts hused hinp
      (E tape) (E tape') (k * L) (Nat.mul_le_mul_right L hk)
      hpreBits (Nat.mul_le_mul_right L hread)
  have haccepted (tape : Fin Nblocks → Fin L → Bool) :
      (((List.ofFn tape).take (usedB tape)).filter
        (fun a => a ∈ FairBitIndices.acceptedBlocks m)).length ≤
          s * attemptsB tape := by
    have hsize : attemptsB tape * (s * t) ≤ Nblocks :=
      (Nat.mul_le_mul_right (s * t) (hattempts (E tape))).trans hblocks
    have hflat := LocalFlatLaw.flatBits_blockTapeBitsEquiv Nblocks L tape
    have h := LocalFlatLaw.FlatRetryExecution.accepted_prefix_le
      m (R (E tape)).hpositive t s
      (LocalFlatLaw.localBadOutputs m s (R (E tape)).domain
        (numericNeighborhood G) groupedB Wbase b)
      (hfull (E tape)) (List.ofFn tape)
      (by simpa [L, ClassRepresentativeTrace.tapeBits] using
        (hbits (E tape)).trans hflat)
      (by simpa using hsize)
    simpa [attemptsB, usedB, Nat.mul_comm] using h
  have hmeanB : (∑ tape : Fin Nblocks → Fin L → Bool, attemptsB tape) ≤
      2 * Fintype.card (Fin L → Bool) ^ Nblocks := by
    have hsum :
        (∑ tape : Fin Nblocks → Fin L → Bool,
          (attemptsB tape : ℚ)) =
        ∑ tape : FlatTraceLaw.FlatTape (Nblocks * L),
          (attempts tape : ℚ) := by
      exact Fintype.sum_equiv E _ _ (by intro tape; rfl)
    have hcard : Fintype.card (Fin L → Bool) ^ Nblocks =
        2 ^ (Nblocks * L) := by
      simp [Fintype.card_fun, ← pow_mul, Nat.mul_comm]
    have hcardQ : (2 ^ (Nblocks * L) : ℚ) =
        (Fintype.card (Fin L → Bool) : ℚ) ^ Nblocks := by
      exact_mod_cast hcard.symm
    have hq : ((∑ tape : Fin Nblocks → Fin L → Bool,
        attemptsB tape : ℕ) : ℚ) ≤
        ((2 * Fintype.card (Fin L → Bool) ^ Nblocks : ℕ) : ℚ) := by
      simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      rw [hsum]
      simpa only [L, hcardQ] using hmean
    exact_mod_cast hq
  have hboundSum := LocalFlatLaw.sum_causalUsed_le_four_trials
    (FairBitIndices.acceptedBlocks m)
    (LocalFlatLaw.acceptedBitBlocks_half m (R (E (fun _ => fun _ => false))).hpositive)
    usedB attemptsB hbound hcausal haccepted hmeanB
  have hsum :
      (∑ tape : Fin Nblocks → Fin L → Bool, usedB tape) =
      ∑ tape : FlatTraceLaw.FlatTape (Nblocks * L), used tape := by
    exact Fintype.sum_equiv E _ _ (by intro tape; rfl)
  have hcard : Fintype.card (Fin L → Bool) ^ Nblocks =
      2 ^ (Nblocks * L) := by
    simp [Fintype.card_fun, ← pow_mul, Nat.mul_comm]
  change (∑ tape : Fin Nblocks → Fin L → Bool, usedB tape) ≤
    4 * s * Fintype.card (Fin L → Bool) ^ Nblocks at hboundSum
  rw [hsum, hcard] at hboundSum
  simpa [L] using hboundSum

lemma localRepairRetriesSource_mean_used_one
    {B n domainCap s t bufferCap targetCap q b Nblocks : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 1) →
      ReadyInput B n 1 domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (attempts used accepted :
      FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 1) → ℕ)
    (hfull : ∀ tape,
      LocalFlatLaw.FlatRetryExecution 1 (R tape).hpositive t s
        (LocalFlatLaw.localBadOutputs 1 s (R tape).domain
          (numericNeighborhood G) groupedB Wbase b)
        (attempts tape) (R tape).bits (used tape) (accepted tape))
    (hmean : (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 1), (attempts tape : ℚ)) ≤
        2 * (2 ^ (Nblocks * Nat.clog 2 1) : ℚ)) :
    (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 1),
      used tape) ≤ 4 * s * 2 ^ (Nblocks * Nat.clog 2 1) := by
  classical
  have hpoint (tape : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 1)) : used tape ≤ s * attempts tape := by
    have h := LocalFlatLaw.FlatRetryExecution.used_le_requests_one
      (R tape).hpositive t s
      (LocalFlatLaw.localBadOutputs 1 s (R tape).domain
        (numericNeighborhood G) groupedB Wbase b) (hfull tape)
    simpa [Nat.mul_comm] using h
  have hsum :
      (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 1),
        used tape) ≤
      s * (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 1), attempts tape) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun tape _ => hpoint tape)
  have hmeanNat :
      (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 1), attempts tape) ≤ 2 := by
    have hq : (((∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 1), attempts tape) : ℕ) : ℚ) ≤ 2 := by
      simpa using hmean
    exact_mod_cast hq
  have hclog : Nat.clog 2 1 = 0 := by norm_num
  simp only [hclog, Nat.mul_zero, pow_zero, mul_one] at *
  nlinarith

/-- Actual local repair retries, on one common finite tape, have source
charge linear in the local draw count and scan allowance. The capped selector
parameter `t` occurs only in the tape reserve, not in the mean charge. -/
lemma localRepairRetriesSource_mean_runtime_stopped_trace
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m) → ℕ)
      (finalState : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m) → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ
        (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
        (finalState tape).vars "repairRetriesLeft" + attempts tape = cap ∧
        (finalState tape).inp =
          ((R tape).bits.drop (used tape * Nat.clog 2 m)).map Bool.toNat ++
            (R tape).rest ∧
        attempts tape ≤ cap ∧ used tape ≤ attempts tape * (s * t)) ∧
      (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m),
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          4 * s * (15 * Nat.clog 2 m + 30) +
          2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m) : ℚ) := by
  classical
  have hbudget : cap * (s * t * Nat.clog 2 m) ≤
      Nblocks * Nat.clog 2 m := by
    have h := Nat.mul_le_mul_right (Nat.clog 2 m) hblocks
    nlinarith
  obtain ⟨attempts, used, accepted, finalState, hsource, hmean⟩ :=
    localRepairRetriesSource_mean_full_trace_le_two domain R hbits
      hdomain hcap hcapB hbudget henum hhalf
  have hrun (tape : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m)) :
      Run B localRepairRetriesSource (R tape).σ (finalState tape)
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14)) := by
    simpa [hscan tape] using (hsource tape).1
  have husedMean :
      (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m),
        used tape) ≤ 4 * s * 2 ^ (Nblocks * Nat.clog 2 m) := by
    by_cases hmone : m = 1
    · subst m
      exact localRepairRetriesSource_mean_used_one R attempts used accepted
        (fun tape => by simpa [hdomain tape] using
          (hsource tape).2.2.2.2.1) hmean
    · have hmpos : 0 < m :=
        (R (Classical.choice (inferInstance : Nonempty
          (FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m))))).hpositive
      have hL : 0 < Nat.clog 2 m :=
        Nat.clog_pos (by decide) (by omega)
      exact localRepairRetriesSource_mean_used_posWidth R hbits hstate
        hblocks hL attempts used accepted finalState
        (fun tape => (hsource tape).1)
        (fun tape => (hsource tape).2.1)
        (fun tape => (hsource tape).2.2.1)
        (fun tape => (hsource tape).2.2.2.1)
        (fun tape => by simpa [hdomain tape] using
          (hsource tape).2.2.2.2.1) hmean
  refine ⟨attempts, used, finalState, ?_, ?_⟩
  · intro tape
    exact ⟨hrun tape, (hsource tape).2.2.2.2.2,
      (hsource tape).2.2.2.1, (hsource tape).2.1,
      (hsource tape).2.2.1⟩
  ·
    have hcount : Fintype.card
        (FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m)) =
          2 ^ (Nblocks * Nat.clog 2 m) := by
      simp [FlatTraceLaw.FlatTape, Fintype.card_fun]
    have husedQ :
        (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m),
          (used tape : ℚ)) ≤
        4 * s * (2 ^ (Nblocks * Nat.clog 2 m) : ℚ) := by
      exact_mod_cast husedMean
    have hsum :
        (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m),
          ((12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) =
        (12 * Nat.clog 2 m + 38 : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m) : ℚ) +
        (15 * Nat.clog 2 m + 30 : ℚ) *
          (∑ tape : FlatTraceLaw.FlatTape
            (Nblocks * Nat.clog 2 m), (used tape : ℚ)) +
        (79 * s + scanUpper + 50 : ℚ) *
          (∑ tape : FlatTraceLaw.FlatTape
            (Nblocks * Nat.clog 2 m), (attempts tape : ℚ)) := by
      simp [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib,
        Finset.mul_sum, hcount]
      simp [mul_comm, mul_left_comm, mul_assoc]
      ring
    rw [hsum]
    have hdrawNonneg : (0 : ℚ) ≤ 15 * Nat.clog 2 m + 30 := by positivity
    have htrialNonneg : (0 : ℚ) ≤ 79 * s + scanUpper + 50 := by positivity
    push_cast
    nlinarith [husedQ, hmean]

lemma localRepairRetriesSource_mean_runtime_stopped
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m) → ℕ)
      (finalState : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m) → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ
        (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14))) ∧
      (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m),
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          4 * s * (15 * Nat.clog 2 m + 30) +
          2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m) : ℚ) := by
  obtain ⟨attempts, used, finalState, htrace, hmean⟩ :=
    localRepairRetriesSource_mean_runtime_stopped_trace domain R hbits
      hstate hdomain hscan hcap hcapB hblocks henum hhalf
  exact ⟨attempts, used, finalState, (fun tape => (htrace tape).1), hmean⟩

/-- Conditioning on an arbitrary unread suffix extends the stopped local
runtime law to a flat tape whose length need not be divisible by the local
selector width. -/
lemma localRepairRetriesSource_mean_runtime_stopped_suffix_trace
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks Ntail scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) → ℕ)
      (finalState : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail) → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ
        (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
        (finalState tape).vars "repairRetriesLeft" + attempts tape = cap ∧
        (finalState tape).inp =
          ((R tape).bits.drop (used tape * Nat.clog 2 m)).map Bool.toNat ++
            (R tape).rest ∧
        attempts tape ≤ cap ∧ used tape ≤ attempts tape * (s * t)) ∧
      (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail),
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          4 * s * (15 * Nat.clog 2 m + 30) +
          2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m + Ntail) : ℚ) := by
  classical
  let P := Nblocks * Nat.clog 2 m
  let E := Fin.appendEquiv (α := Bool) P Ntail
  let Rpre (suffix : FlatTraceLaw.FlatTape Ntail)
      (preTape : FlatTraceLaw.FlatTape P) :
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent :=
    let full := E (preTape, suffix)
    let base := R full
    { base with
      bits := FlatTraceLaw.flatBits preTape
      rest := (FlatTraceLaw.flatBits suffix).map Bool.toNat ++ base.rest
      hinput := by
        rw [base.hinput, hbits full]
        have he : full = Fin.append preTape suffix := rfl
        rw [he]
        simp [FlatTraceLaw.flatBits, List.ofFn_fin_append,
          List.map_append, List.append_assoc] }
  have hfamily (suffix : FlatTraceLaw.FlatTape Ntail) :
      ∃ (attempts used : FlatTraceLaw.FlatTape P → ℕ)
        (finalState : FlatTraceLaw.FlatTape P → Env),
        (∀ preTape, Run B localRepairRetriesSource
          (Rpre suffix preTape).σ (finalState preTape)
            (12 * Nat.clog 2 m + 24 +
              ((15 * Nat.clog 2 m + 30) * used preTape +
                attempts preTape * (79 * s + scanUpper + 50) + 14)) ∧
          (finalState preTape).vars "repairRetriesLeft" + attempts preTape = cap ∧
          (finalState preTape).inp =
            ((Rpre suffix preTape).bits.drop
              (used preTape * Nat.clog 2 m)).map Bool.toNat ++
              (Rpre suffix preTape).rest ∧
          attempts preTape ≤ cap ∧
          used preTape ≤ attempts preTape * (s * t)) ∧
        (∑ preTape : FlatTraceLaw.FlatTape P,
          ((12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used preTape +
              attempts preTape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
          ((12 * Nat.clog 2 m + 38 +
            4 * s * (15 * Nat.clog 2 m + 30) +
            2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
            (2 ^ P : ℚ) := by
    have hpreBits : ∀ preTape, (Rpre suffix preTape).bits =
        FlatTraceLaw.flatBits preTape := by intro preTape; rfl
    have hpreState : ∀ preTape preTape',
        (Rpre suffix preTape).σ.vars = (Rpre suffix preTape').σ.vars ∧
        (Rpre suffix preTape).σ.arrs = (Rpre suffix preTape').σ.arrs ∧
        (Rpre suffix preTape).σ.out = (Rpre suffix preTape').σ.out := by
      intro preTape preTape'
      exact hstate (E (preTape, suffix)) (E (preTape', suffix))
    exact localRepairRetriesSource_mean_runtime_stopped_trace domain
      (Rpre suffix) hpreBits hpreState
      (fun preTape => hdomain (E (preTape, suffix)))
      (fun preTape => hscan (E (preTape, suffix)))
      (fun preTape => hcap (E (preTape, suffix)))
      hcapB hblocks henum hhalf
  choose attemptsP usedP finalP hrunP hmeanP using hfamily
  let attempts (full : FlatTraceLaw.FlatTape (P + Ntail)) : ℕ :=
    attemptsP (E.symm full).2 (E.symm full).1
  let used (full : FlatTraceLaw.FlatTape (P + Ntail)) : ℕ :=
    usedP (E.symm full).2 (E.symm full).1
  let finalState (full : FlatTraceLaw.FlatTape (P + Ntail)) : Env :=
    finalP (E.symm full).2 (E.symm full).1
  refine ⟨attempts, used, finalState, ?_, ?_⟩
  · intro full
    obtain ⟨h, hcount, hinp, ha, hu⟩ :=
      hrunP (E.symm full).2 (E.symm full).1
    have he : E ((E.symm full).1, (E.symm full).2) = full :=
      E.apply_symm_apply full
    change Run B localRepairRetriesSource
      (R (E ((E.symm full).1, (E.symm full).2))).σ
      (finalState full)
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used full +
            attempts full * (79 * s + scanUpper + 50) + 14)) at h
    rw [he] at h
    refine ⟨h, hcount, ?_, ha, hu⟩
    have husedBits : used full * Nat.clog 2 m ≤ P := by
      calc
        used full * Nat.clog 2 m ≤
            (attempts full * (s * t)) * Nat.clog 2 m :=
          Nat.mul_le_mul_right _ hu
        _ ≤ (cap * (s * t)) * Nat.clog 2 m := by
          gcongr
        _ ≤ P := Nat.mul_le_mul_right _ hblocks
    have hsplit : FlatTraceLaw.flatBits full =
        FlatTraceLaw.flatBits (E.symm full).1 ++
          FlatTraceLaw.flatBits (E.symm full).2 := by
      rw [← he]
      simp [FlatTraceLaw.flatBits, E, List.ofFn_add]
    have hlen : used full * Nat.clog 2 m ≤
        (FlatTraceLaw.flatBits (E.symm full).1).length := by
      simpa [FlatTraceLaw.flatBits_length, P] using husedBits
    rw [hbits full, hsplit]
    simpa only [Rpre, List.map_drop, List.map_append,
      List.drop_append_of_le_length hlen, List.append_assoc, he] using hinp
  · have hsum :
        (∑ full : FlatTraceLaw.FlatTape (P + Ntail),
          ((12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used full +
              attempts full * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) =
        ∑ suffix : FlatTraceLaw.FlatTape Ntail,
          ∑ preTape : FlatTraceLaw.FlatTape P,
            ((12 * Nat.clog 2 m + 24 +
              ((15 * Nat.clog 2 m + 30) * usedP suffix preTape +
                attemptsP suffix preTape *
                  (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ) := by
      calc
        _ = ∑ pair : FlatTraceLaw.FlatTape P ×
            FlatTraceLaw.FlatTape Ntail,
            ((12 * Nat.clog 2 m + 24 +
              ((15 * Nat.clog 2 m + 30) *
                usedP pair.2 pair.1 +
                attemptsP pair.2 pair.1 *
                  (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ) := by
              exact Fintype.sum_equiv E.symm _ _
                (by intro full; simp [attempts, used])
        _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [hsum]
    have htotal := Finset.sum_le_sum
      (s := (Finset.univ : Finset (FlatTraceLaw.FlatTape Ntail)))
      (fun suffix _ => hmeanP suffix)
    have hcard : Fintype.card (FlatTraceLaw.FlatTape Ntail) =
        2 ^ Ntail := by simp [FlatTraceLaw.FlatTape, Fintype.card_fun]
    simpa [P, pow_add, hcard, mul_assoc, mul_comm, mul_left_comm]
      using htotal

lemma localRepairRetriesSource_mean_runtime_stopped_suffix
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks Ntail scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) → ℕ)
      (finalState : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail) → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ
        (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14))) ∧
      (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail),
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          4 * s * (15 * Nat.clog 2 m + 30) +
          2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m + Ntail) : ℚ) := by
  obtain ⟨attempts, used, finalState, htrace, hmean⟩ :=
    localRepairRetriesSource_mean_runtime_stopped_suffix_trace domain R hbits
      hstate hdomain hscan hcap hcapB hblocks henum hhalf
  exact ⟨attempts, used, finalState, (fun tape => (htrace tape).1), hmean⟩

/-- The paper hypotheses use neighborhoods restricted to the active set;
the source scans physical CSR rows. This theorem connects them without
requiring any full graph neighborhood to lie in the active set. -/
lemma localRepairRetriesSource_mean_runtime_restricted_paper
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent A : Finset ℕ}
    (r k c : ℕ)
    (choice : SamplerPhases.InitialChoice A groupedB
      (fun v => numericNeighborhood G v ∩ A) r)
    (as : List ℕ) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hinj : ∀ u ∈ groupedB, ∀ v ∈ groupedB,
      numericNeighborhood G u ∩ A = numericNeighborhood G v ∩ A → u = v)
    (hb : b ∈ groupedB)
    (hfar : 2 * k < 3 * SamplerPhases.disagreement
      (fun v => numericNeighborhood G v ∩ A) b (choice.representative b))
    (hc : 2 ≤ c)
    (hshatter : ∀ Y : Finset ℕ, Y ⊆ A → Y.Nonempty →
      (SamplerPhases.traceClasses
        (fun v => numericNeighborhood G v ∩ A) Y groupedB).card ≤
          c * Y.card)
    (hX : X = ((numericNeighborhood G b ∩ A) \
      (numericNeighborhood G (choice.representative b) ∩ A)) ∪
      ((numericNeighborhood G (choice.representative b) ∩ A) \
        (numericNeighborhood G b ∩ A)))
    (hW : Wbase = SamplerPhases.phase2Scan
      (fun v => numericNeighborhood G v ∩ A)
        (choice.exceptions k) as choice.sample)
    (hs : s = 64 * Nat.clog 2 c)
    (hWA : Wbase ⊆ A)
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (henum : PrefixEnumerates m domain X) :
    ∃ (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m) → ℕ)
      (finalState : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m) → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ
        (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14))) ∧
      (∑ tape : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m),
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          4 * s * (15 * Nat.clog 2 m + 30) +
          2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m) : ℚ) := by
  have hhalf := LocalFlatLaw.localFailure_half_restricted_paper
    A groupedB Wbase X (numericNeighborhood G) r k c b s choice as
    has hasNodup hinj hb hfar hc hshatter hX hW hs hWA
  exact localRepairRetriesSource_mean_runtime_stopped domain R hbits
    hstate hdomain hscan hcap hcapB hblocks henum hhalf

/-- With a fixed scan upper bound, the weighted scan term in the actual
source retry-run charge has mean at most twice one trial's scan allowance. -/
lemma localRepairRetriesSource_mean_scan_charge_le_two
    {B n m domainCap s t bufferCap targetCap q b cap Nbits scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape Nbits →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ Nbits)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (Lax457868Proofs.SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ attempts : FlatTraceLaw.FlatTape Nbits → ℕ,
      (∀ tape, attempts tape ≤ cap ∧
        ∃ (σ' : Env) (totalUsed : ℕ),
          Run B localRepairRetriesSource (R tape).σ σ'
            (12 * Nat.clog 2 m + 24 +
              ((15 * Nat.clog 2 m + 30) * totalUsed +
                attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
          totalUsed ≤ attempts tape * (s * t)) ∧
      (∑ tape : FlatTraceLaw.FlatTape Nbits, (attempts tape : ℚ)) ≤
        2 * (2 ^ Nbits : ℚ) ∧
      (∑ tape : FlatTraceLaw.FlatTape Nbits,
        (attempts tape * scanUpper : ℚ)) ≤
          2 * scanUpper * (2 ^ Nbits : ℚ) := by
  obtain ⟨attempts, hrun, hmean⟩ :=
    localRepairRetriesSource_mean_attempts_le_two domain R hbits hdomain
      hcap hcapB hbudget henum hhalf
  refine ⟨attempts, ?_, hmean, ?_⟩
  · intro tape
    obtain ⟨hattempts, σ', totalUsed, hsource, hused⟩ := hrun tape
    refine ⟨hattempts, σ', totalUsed, ?_, hused⟩
    simpa [hscan tape] using hsource
  · have hnonneg : (0 : ℚ) ≤ scanUpper := by positivity
    have hsum : (∑ tape : FlatTraceLaw.FlatTape Nbits,
        (attempts tape * scanUpper : ℚ)) =
        (scanUpper : ℚ) *
          (∑ tape : FlatTraceLaw.FlatTape Nbits, (attempts tape : ℚ)) := by
      simp [Finset.mul_sum, mul_comm]
    rw [hsum]
    nlinarith [hmean]

/-- The paired-swap local failure estimate supplies the half premise for the
actual retry source family, yielding the two-trial and scan-charge bounds. -/
lemma localRepairRetriesSource_mean_scan_charge_paper
    {B n m domainCap s t bufferCap targetCap q b cap Nbits scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent A : Finset ℕ}
    (r k c : ℕ)
    (choice : SamplerPhases.InitialChoice A groupedB
      (numericNeighborhood G) r)
    (as : List ℕ) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ v ∈ groupedB, numericNeighborhood G v ⊆ A)
    (hinj : ∀ u ∈ groupedB, ∀ v ∈ groupedB,
      numericNeighborhood G u = numericNeighborhood G v → u = v)
    (hb : b ∈ groupedB)
    (hfar : 2 * k < 3 * SamplerPhases.disagreement
      (numericNeighborhood G) b (choice.representative b))
    (hc : 2 ≤ c)
    (hshatter : ∀ Y : Finset ℕ, Y ⊆ A → Y.Nonempty →
      (SamplerPhases.traceClasses (numericNeighborhood G) Y groupedB).card ≤
        c * Y.card)
    (hX : X = (numericNeighborhood G b \ numericNeighborhood G
      (choice.representative b)) ∪
      (numericNeighborhood G (choice.representative b) \
        numericNeighborhood G b))
    (hW : Wbase = SamplerPhases.phase2Scan (numericNeighborhood G)
      (choice.exceptions k) as choice.sample)
    (hs : s = 64 * Nat.clog 2 c)
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape Nbits →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ Nbits)
    (henum : PrefixEnumerates m domain X) :
    ∃ attempts : FlatTraceLaw.FlatTape Nbits → ℕ,
      (∀ tape, attempts tape ≤ cap ∧
        ∃ (σ' : Env) (totalUsed : ℕ),
          Run B localRepairRetriesSource (R tape).σ σ'
            (12 * Nat.clog 2 m + 24 +
              ((15 * Nat.clog 2 m + 30) * totalUsed +
                attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
          totalUsed ≤ attempts tape * (s * t)) ∧
      (∑ tape : FlatTraceLaw.FlatTape Nbits, (attempts tape : ℚ)) ≤
        2 * (2 ^ Nbits : ℚ) ∧
      (∑ tape : FlatTraceLaw.FlatTape Nbits,
        (attempts tape * scanUpper : ℚ)) ≤
          2 * scanUpper * (2 ^ Nbits : ℚ) := by
  have hsingle := SamplerLocalSuccess.localTrial_failure_lt_half
    A groupedB (numericNeighborhood G) r k c choice as has hasNodup
    hN hinj b hb hfar hc hshatter
  have hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s := by
    subst X
    subst Wbase
    subst s
    exact Nat.le_of_lt hsingle
  exact localRepairRetriesSource_mean_scan_charge_le_two domain R hbits
    hdomain hscan hcap hcapB hbudget henum hhalf

/-- The actual source charge, including draw work and fixed setup, has the
two-trial average bound under the paper's local failure hypotheses. -/
lemma localRepairRetriesSource_mean_runtime_paper
    {B n m domainCap s t bufferCap targetCap q b cap Nbits scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent A : Finset ℕ}
    (r k c : ℕ)
    (choice : SamplerPhases.InitialChoice A groupedB
      (numericNeighborhood G) r)
    (as : List ℕ) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ v ∈ groupedB, numericNeighborhood G v ⊆ A)
    (hinj : ∀ u ∈ groupedB, ∀ v ∈ groupedB,
      numericNeighborhood G u = numericNeighborhood G v → u = v)
    (hb : b ∈ groupedB)
    (hfar : 2 * k < 3 * SamplerPhases.disagreement
      (numericNeighborhood G) b (choice.representative b))
    (hc : 2 ≤ c)
    (hshatter : ∀ Y : Finset ℕ, Y ⊆ A → Y.Nonempty →
      (SamplerPhases.traceClasses (numericNeighborhood G) Y groupedB).card ≤
        c * Y.card)
    (hX : X = (numericNeighborhood G b \ numericNeighborhood G
      (choice.representative b)) ∪
      (numericNeighborhood G (choice.representative b) \
        numericNeighborhood G b))
    (hW : Wbase = SamplerPhases.phase2Scan (numericNeighborhood G)
      (choice.exceptions k) as choice.sample)
    (hs : s = 64 * Nat.clog 2 c)
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape Nbits →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hdomain : ∀ tape, (R tape).domain = domain)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hbudget : cap * (s * t * Nat.clog 2 m) ≤ Nbits)
    (henum : PrefixEnumerates m domain X) :
    ∃ (attempts totalUsed : FlatTraceLaw.FlatTape Nbits → ℕ)
      (finalState : FlatTraceLaw.FlatTape Nbits → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ (finalState tape)
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * totalUsed tape +
            attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
        totalUsed tape ≤ attempts tape * (s * t)) ∧
      (∑ tape : FlatTraceLaw.FlatTape Nbits,
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * totalUsed tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          2 * ((15 * Nat.clog 2 m + 30) * (s * t) +
            79 * s + scanUpper + 50) : ℕ) : ℚ) * (2 ^ Nbits : ℚ) := by
  classical
  obtain ⟨attempts, hsource, hmean, _⟩ :=
    localRepairRetriesSource_mean_scan_charge_paper r k c choice as has
      hasNodup hN hinj hb hfar hc hshatter hX hW hs domain R hbits
      hdomain hscan hcap hcapB hbudget henum
  have hex : ∀ tape : FlatTraceLaw.FlatTape Nbits,
      ∃ (finalState : Env) (totalUsed : ℕ),
        Run B localRepairRetriesSource (R tape).σ finalState
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * totalUsed +
              attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
        totalUsed ≤ attempts tape * (s * t) := by
    intro tape
    obtain ⟨_, finalState, totalUsed, hrun, hused⟩ := hsource tape
    exact ⟨finalState, totalUsed, hrun, hused⟩
  choose finalState totalUsed hchosen using hex
  refine ⟨attempts, totalUsed, finalState, hchosen, ?_⟩
  let setup : ℕ := 12 * Nat.clog 2 m + 38
  let trial : ℕ := (15 * Nat.clog 2 m + 30) * (s * t) +
    79 * s + scanUpper + 50
  have hpoint (tape : FlatTraceLaw.FlatTape Nbits) :
      12 * Nat.clog 2 m + 24 +
        ((15 * Nat.clog 2 m + 30) * totalUsed tape +
          attempts tape * (79 * s + scanUpper + 50) + 14) ≤
      setup + attempts tape * trial := by
    have hmul := Nat.mul_le_mul_left (15 * Nat.clog 2 m + 30)
      (hchosen tape).2
    dsimp [setup, trial]
    nlinarith
  have hsum :
      (∑ tape : FlatTraceLaw.FlatTape Nbits,
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * totalUsed tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
      ∑ tape : FlatTraceLaw.FlatTape Nbits,
        ((setup + attempts tape * trial : ℕ) : ℚ) := by
    apply Finset.sum_le_sum
    intro tape _
    exact_mod_cast hpoint tape
  have hcount : Fintype.card (FlatTraceLaw.FlatTape Nbits) = 2 ^ Nbits := by
    simp [FlatTraceLaw.FlatTape, Fintype.card_fun]
  have hsumEq :
      (∑ tape : FlatTraceLaw.FlatTape Nbits,
        ((setup + attempts tape * trial : ℕ) : ℚ)) =
      (setup : ℚ) * (2 ^ Nbits : ℚ) +
        (trial : ℚ) *
          ∑ tape : FlatTraceLaw.FlatTape Nbits, (attempts tape : ℚ) := by
    simp [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib,
      Finset.mul_sum, hcount, mul_comm]
  rw [hsumEq] at hsum
  have htrialNonneg : (0 : ℚ) ≤ trial := by positivity
  have hbound :
      (setup : ℚ) * (2 ^ Nbits : ℚ) +
        (trial : ℚ) *
          (∑ tape : FlatTraceLaw.FlatTape Nbits, (attempts tape : ℚ)) ≤
      ((setup + 2 * trial : ℕ) : ℚ) * (2 ^ Nbits : ℚ) := by
    push_cast
    nlinarith [hmean]
  exact hsum.trans (by simpa [setup, trial] using hbound)

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
lemma localRepairOneException_run_far_trace
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
          σ'.arrs "sampleFlags" = arrOf n (setFlag Wcurrent))) ∧
      ∃ Rafter : ReadyInput B n X.card n s t bufferCap targetCap q b
          G x X groupedB Wbase Wcurrent,
        Run B repairDomainSource P.σ Rafter.σ
          (54 * ((offset x (b + 1) - offset x b) +
            (offset x (rep b + 1) - offset x (rep b))) +
            36 * (((numericNeighborhood G b ∩ A).card) +
              ((numericNeighborhood G (rep b) ∩ A).card)) + 73) ∧
        Rafter.bits = P.bits ∧ Rafter.rest = P.rest ∧
        Rafter.scanUpper = P.scanUpper ∧
        Run B localRepairRetriesSource Rafter.σ σ'
          (12 * Nat.clog 2 X.card + 24 +
            ((15 * Nat.clog 2 X.card + 30) * totalUsed +
              attempts * (79 * s + P.scanUpper + 50) + 14)) ∧
        (∃ rejected : ℕ,
          rejected ≤ attempts ∧ attempts ≤ rejected + 1 ∧
          FlatRejectedTrials X.card t s
            (localBadOutputs X.card s Rafter.domain
              (numericNeighborhood G) groupedB Wbase b)
            rejected Rafter.bits) ∧
        (∃ accepted : ℕ,
          FlatRetryExecution X.card Rafter.hpositive t s
            (localBadOutputs X.card s Rafter.domain
              (numericNeighborhood G) groupedB Wbase b)
            attempts Rafter.bits totalUsed accepted) ∧
        σ'.vars "repairRetriesLeft" + attempts = cap := by
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
    hinp, hn', hqpow, htrial, hrow, hdesired, hout,
    hreject, hfull, hcount⟩ :=
    localRepairRetriesSource_run_trace Rafter hcapAfter hcapB hbudget
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
    hinp, hn', ?_, htrial, hrow, hdesired, ?_, ?_, hout, ?_⟩
  · simpa [localRepairOneExceptionSource] using rd.seq rite
  · exact hqpow.trans (rd.frame_var "qpow" (by decide))
  · exact (rr.frame_arr "repairBMarks" (by decide)).trans hBmarks
  · exact (rr.frame_arr "repairRMarks" (by decide)).trans hRmarks
  · exact ⟨Rafter, rd, rfl, rfl, rfl, rr, hreject, hfull, hcount⟩

/-- Preserve the original far-branch interface for clients that only need
the final source state. -/
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
  obtain ⟨σ', attempts, totalUsed, hr, ha, hu, hinp, hn, hq,
    htrial, hrow, hdesired, hBmarks, hRmarks, hout, _⟩ :=
    localRepairOneException_run_far_trace P hA hrep hactive hbmarks
      hrmarks hblist hrlist hr hXeq hfar hfarB hfarCase hcap hcapB
      hpowB hbudget
  exact ⟨σ', attempts, totalUsed, hr, ha, hu, hinp, hn, hq,
    htrial, hrow, hdesired, hBmarks, hRmarks, hout⟩

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

/-- Only occupied domain-buffer cells affect a retry. Replace the arbitrary
function used to represent the fixed array by a common one, preserving every
source state and all positive-prefix enumeration facts. -/
def ReadyInput.retarget_domain
    {B n m domainCap s t bufferCap targetCap q b : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    (domain : ℕ → ℕ)
    (hagree : ∀ j < domainCap, R.domain j = domain j) :
    ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent := by
  have hlist : Stack.toList m R.domain = Stack.toList m domain := by
    apply List.ext_getElem
    · simp [Stack.toList]
    · intro i hi hi'
      have him : i < m := by simpa [Stack.toList] using hi
      have hic : i < domainCap := him.trans_le R.hdomainCap
      simpa [Stack.toList] using hagree i hic
  have henum : PrefixEnumerates m domain X := by
    simpa only [PrefixEnumerates, ← hlist] using R.henum
  exact { R with
    domain := domain
    hdomain := R.hdomain.trans (arrOf_congr hagree)
    henum := henum }

/-- The local mean theorem only needs a common domain on occupied buffer
indices. It does not require arbitrary values beyond `domainCap` to agree. -/
lemma localRepairRetriesSource_mean_runtime_stopped_suffix_domain_prefix_trace
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks Ntail scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hdomain : ∀ tape j, j < domainCap → (R tape).domain j = domain j)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ (attempts used : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail) → ℕ)
      (finalState : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail) → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ
        (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
        (finalState tape).vars "repairRetriesLeft" + attempts tape = cap ∧
        (finalState tape).inp =
          ((R tape).bits.drop (used tape * Nat.clog 2 m)).map Bool.toNat ++
            (R tape).rest ∧
        attempts tape ≤ cap ∧ used tape ≤ attempts tape * (s * t)) ∧
      (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail),
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          4 * s * (15 * Nat.clog 2 m + 30) +
          2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m + Ntail) : ℚ) := by
  let R' (tape : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail)) :=
    ReadyInput.retarget_domain (R tape) domain (hdomain tape)
  simpa only [R', ReadyInput.retarget_domain] using
    (localRepairRetriesSource_mean_runtime_stopped_suffix_trace domain R'
      (fun tape => hbits tape) hstate
      (fun _ => rfl) hscan hcap hcapB hblocks henum hhalf)

lemma localRepairRetriesSource_mean_runtime_stopped_suffix_domain_prefix
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks Ntail scanUpper : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (R : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ tape, (R tape).bits = FlatTraceLaw.flatBits tape)
    (hstate : ∀ tape tape',
      (R tape).σ.vars = (R tape').σ.vars ∧
      (R tape).σ.arrs = (R tape').σ.arrs ∧
      (R tape).σ.out = (R tape').σ.out)
    (hdomain : ∀ tape j, j < domainCap → (R tape).domain j = domain j)
    (hscan : ∀ tape, (R tape).scanUpper = scanUpper)
    (hcap : ∀ tape, (R tape).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s) :
    ∃ (attempts used : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail) → ℕ)
      (finalState : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail) → Env),
      (∀ tape, Run B localRepairRetriesSource (R tape).σ
        (finalState tape)
          (12 * Nat.clog 2 m + 24 +
            ((15 * Nat.clog 2 m + 30) * used tape +
              attempts tape * (79 * s + scanUpper + 50) + 14))) ∧
      (∑ tape : FlatTraceLaw.FlatTape
        (Nblocks * Nat.clog 2 m + Ntail),
        ((12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14) : ℕ) : ℚ)) ≤
        ((12 * Nat.clog 2 m + 38 +
          4 * s * (15 * Nat.clog 2 m + 30) +
          2 * (79 * s + scanUpper + 50) : ℕ) : ℚ) *
          (2 ^ (Nblocks * Nat.clog 2 m + Ntail) : ℚ) := by
  let R' (tape : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail)) :=
    ReadyInput.retarget_domain (R tape) domain (hdomain tape)
  simpa only [R', ReadyInput.retarget_domain] using
    (localRepairRetriesSource_mean_runtime_stopped_suffix domain R'
      (fun tape => hbits tape) hstate
      (fun _ => rfl) hscan hcap hcapB hblocks henum hhalf)

end
end Lax457868Proofs.LocalRepairRetriesSource
