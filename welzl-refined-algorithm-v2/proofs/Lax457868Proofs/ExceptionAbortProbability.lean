import Lax457868Proofs.ExceptionRepairLoop
import Lax457868Proofs.LocalSelectorAbort
import Lax457868Proofs.ExceptionRepairMean
import Lax457868Proofs.StoppedPrefixAveraging

/-! Actual chronological failure certificates for the phase-three repair loop. -/

namespace Lax457868Proofs.ExceptionAbortProbability

open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax808846Proofs.Imp
open Lax808846Proofs.Reasoning
open scoped symmDiff

/-- If a chronological source chain starts without a failure and ends in
status two or three, one of its actual far calls first produced that status. -/
lemma StepChain.failed_far_step
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps)
    (hstart : R.σ.vars "repairRetryStatus" ≠ 2 ∧
      R.σ.vars "repairRetryStatus" ≠ 3)
    (hfinal : σfinal.vars "repairRetryStatus" = 2 ∨
      σfinal.vars "repairRetryStatus" = 3) :
    ∃ z ∈ steps, ∃ (W Wnext : Finset ℕ)
      (Rcur : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A W)
      (Rnext : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wnext)
      (i : ℕ),
      z.vertex = Rcur.exceptionList i ∧
      FarStepTrace Rcur i z.attempts z.used ∧
      (Rnext.σ.vars "repairRetryStatus" = 2 ∨
        Rnext.σ.vars "repairRetryStatus" = 3) ∧
      FarStepFailureTrace Rcur i z.attempts z.used
        (Rnext.σ.vars "repairRetryStatus") := by
  induction hchain with
  | nil R hguard =>
      rcases hfinal with h2 | h3
      · exact False.elim (hstart.1 h2)
      · exact False.elim (hstart.2 h3)
  | cons R Rnext i z tail hindex hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace htail ih =>
      by_cases hnext : Rnext.σ.vars "repairRetryStatus" = 2 ∨
          Rnext.σ.vars "repairRetryStatus" = 3
      · refine ⟨z, by simp, _, _, R, Rnext, i, hvertex, ?_, hnext,
          hfailureTrace hnext⟩
        exact hfar (hfailedFar hnext)
      · obtain ⟨z', hz', W, Wnext', Rcur, Rnext', j, hvertex',
          hfar', hfailed', hfailure'⟩ := ih ⟨by tauto, by tauto⟩ hfinal
        exact ⟨z', by simp [hz'], W, Wnext', Rcur, Rnext', j,
          hvertex', hfar', hfailed', hfailure'⟩

/-- A fixed number of source body calls, independent of the sampled trace. -/
def repeatRepairBody : ℕ → Com
  | 0 => .skip
  | j + 1 => exceptionRepairBody.seq (repeatRepairBody j)

/-- An initial segment of actual exception calls. It need not terminate the
while loop, so it carries no false guard at its endpoint. -/
inductive StepPrefix
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A : Finset ℕ} :
    {W : Finset ℕ} →
      LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A W → Env → List ExecutedException → Prop
  | nil (R) : StepPrefix R R.σ []
  | cons {W Wnext : Finset ℕ}
      (R : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A W)
      (Rnext : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wnext)
      (i : ℕ) (z : ExecutedException) (tail : List ExecutedException)
      (hindex : R.σ.vars "exceptionIndex" = i)
      (hguard : (Cond.lt (.var "exceptionIndex")
        (.var "exceptionStop")).evalB B R.σ = some true)
      (hvertex : z.vertex = R.exceptionList i)
      (hbody : ∃ K, Run B exceptionRepairBody R.σ Rnext.σ K)
      (hbits : Rnext.bits = R.bits.drop
        (ExecutedException.bitCost G A R.rep z))
      (hfixed : SameFixed R Rnext)
      {σfinal : Env} (htail : StepPrefix Rnext σfinal tail) :
      StepPrefix R σfinal (z :: tail)

lemma StepPrefix.repeat_run
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hprefix : StepPrefix R σfinal steps) :
    ∃ K, Run B (repeatRepairBody steps.length) R.σ σfinal K := by
  induction hprefix with
  | nil R => exact ⟨1, by simpa [repeatRepairBody] using
        (Run.skip : Run B .skip R.σ R.σ 1)⟩
  | cons R Rnext i z tail hindex hguard hvertex hbody hbits hfixed htail ih =>
      obtain ⟨K, hrun⟩ := hbody
      obtain ⟨L, htailRun⟩ := ih
      exact ⟨K + L, by
        simpa [repeatRepairBody, List.length_cons, Nat.add_assoc] using
          hrun.seq htailRun⟩

lemma StepChain.repeat_run
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps) :
    ∃ K, Run B (repeatRepairBody steps.length) R.σ σfinal K := by
  induction hchain with
  | nil R hguard => exact ⟨1, by simpa [repeatRepairBody] using
        (Run.skip : Run B .skip R.σ R.σ 1)⟩
  | cons R Rnext i z tail hindex hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace htail ih =>
      obtain ⟨K, hrun⟩ := hbody
      obtain ⟨L, htailRun⟩ := ih
      exact ⟨K + L, by
        simpa [repeatRepairBody, List.length_cons, Nat.add_assoc] using
          hrun.seq htailRun⟩

/-- Every chronological pref can be cut at its actual post-call state. -/
lemma StepChain.split_at
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps) :
    ∀ j ≤ steps.length, ∃ (Wmid : Finset ℕ)
      (Rmid : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wmid)
      (pref suffix : List ExecutedException),
      steps = pref ++ suffix ∧ pref.length = j ∧
      StepPrefix R Rmid.σ pref ∧ StepChain Rmid σfinal suffix ∧
      Rmid.rep = R.rep ∧ Rmid.rest = R.rest ∧
      Rmid.bits = R.bits.drop (traceBitCost G A R.rep pref) := by
  induction hchain with
  | nil R hguard =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      exact ⟨_, R, [], [], rfl, rfl, StepPrefix.nil R,
        StepChain.nil R hguard, rfl, rfl, by simp [traceBitCost]⟩
  | cons R Rnext i z tail hindex hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace htail ih =>
      intro j hj
      cases j with
      | zero =>
          exact ⟨_, R, [], z :: tail, rfl, rfl,
            StepPrefix.nil R,
            StepChain.cons R Rnext i z tail hindex hguard hvertex hbody hbits
              hfixed hfar hfailedFar hfailureTrace htail,
            rfl, rfl, by simp [traceBitCost]⟩
      | succ j =>
          obtain ⟨Wmid, Rmid, pref, suffix, heq, hlen,
            hpref, hsuffix, hrep, hrest, hbitsPref⟩ :=
            ih j (by simpa using hj)
          refine ⟨Wmid, Rmid, z :: pref, suffix, ?_, ?_, ?_, hsuffix,
            ?_, ?_, ?_⟩
          · simp [heq]
          · simp [hlen]
          · exact StepPrefix.cons R Rnext i z pref hindex hguard hvertex hbody
              hbits hfixed hpref
          · exact hrep.trans hfixed.2.1
          · exact hrest.trans hfixed.2.2.2.2.2.1
          · rw [hbitsPref, hfixed.2.1, hbits]
            simp [traceBitCost, ExecutedException.bitCost, List.drop_drop,
              Nat.add_comm, Nat.add_assoc]

/-- Two realized prefixes of the same number of exception-body calls replay
to identical non-input states when their consumed Boolean prefix agrees. -/
lemma StepChain.prefix_replay
    {B n s t bufferCap targetCap q cap k e j : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart Wρ Wτ : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (bits other : List Bool)
    (Pρ : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wρ)
    (Pτ : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wτ)
    (prefρ prefτ : List ExecutedException)
    (hchainρ : StepPrefix (R.reinput bits) Pρ.σ prefρ)
    (hchainτ : StepPrefix (R.reinput other) Pτ.σ prefτ)
    (hlenρ : prefρ.length = j) (hlenτ : prefτ.length = j)
    (hrestρ : Pρ.rest = R.rest) (hrestτ : Pτ.rest = R.rest)
    (hbitsρ : Pρ.bits = bits.drop (traceBitCost G A R.rep prefρ))
    (hbitsτ : Pτ.bits = other.drop (traceBitCost G A R.rep prefτ))
    (hboundρ : traceBitCost G A R.rep prefρ ≤ other.length)
    (hboundτ : traceBitCost G A R.rep prefτ ≤ other.length)
    (hprefix : bits.take (traceBitCost G A R.rep prefρ) =
      other.take (traceBitCost G A R.rep prefρ)) :
    traceBitCost G A R.rep prefτ = traceBitCost G A R.rep prefρ ∧
      Pτ.σ = {Pρ.σ with inp :=
        (other.drop (traceBitCost G A R.rep prefρ)).map Bool.toNat ++
          R.rest} := by
  obtain ⟨K, hrunρ⟩ := StepPrefix.repeat_run hchainρ
  obtain ⟨J, hrunτ⟩ := StepPrefix.repeat_run hchainτ
  have hstartρ : (R.reinput bits).σ =
      {R.σ with inp := bits.map Bool.toNat ++ R.rest} :=
    LoopInput.reinput_state R bits
  have hstartτ : (R.reinput other).σ =
      {R.σ with inp := other.map Bool.toNat ++ R.rest} :=
    LoopInput.reinput_state R other
  have hendρ : Pρ.σ.inp =
      (bits.drop (traceBitCost G A R.rep prefρ)).map Bool.toNat ++
        R.rest := by
    rw [Pρ.hinput, hbitsρ, hrestρ]
  have hendτ : Pτ.σ.inp =
      (other.drop (traceBitCost G A R.rep prefτ)).map Bool.toNat ++
        R.rest := by
    rw [Pτ.hinput, hbitsτ, hrestτ]
  have hrunρ' : Run B (repeatRepairBody j)
      {R.σ with inp := bits.map Bool.toNat ++ R.rest} Pρ.σ K := by
    simpa [hstartρ, hlenρ] using hrunρ
  have hrunτ' : Run B (repeatRepairBody j)
      {R.σ with inp := other.map Bool.toNat ++ R.rest} Pτ.σ J := by
    simpa [hstartτ, hlenτ] using hrunτ
  exact StoppedPrefixAveraging.bool_run_same_prefix bits other R.rest
    hrunρ' hrunτ' hendρ hendτ hboundρ hboundτ hprefix

end Lax457868Proofs.ExceptionAbortProbability
