import Lax457868Proofs.ExceptionRepairLoop
import Lax457868Proofs.LocalSelectorAbort
import Lax457868Proofs.ExceptionRepairMean
import Lax457868Proofs.ExceptionLoopMean
import Lax457868Proofs.PackedRepairTrace
import Lax457868Proofs.StoppedPrefixAveraging

/-! Actual chronological failure certificates for the phase-three repair loop. -/

set_option maxHeartbeats 2000000

namespace Lax457868Proofs.ExceptionAbortProbability

open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.LocalRepairSource
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax808846Proofs.Imp
open Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
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
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace hfailedStop htail ih =>
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

lemma StepPrefix.split_at
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hprefix : StepPrefix R σfinal steps) :
    ∀ j ≤ steps.length, ∃ (Wmid : Finset ℕ)
      (Rmid : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wmid)
      (pref suffix : List ExecutedException),
      steps = pref ++ suffix ∧ pref.length = j ∧
      StepPrefix R Rmid.σ pref ∧ StepPrefix Rmid σfinal suffix ∧
      Rmid.rep = R.rep ∧ Rmid.rest = R.rest ∧
      Rmid.bits = R.bits.drop (traceBitCost G A R.rep pref) := by
  induction hprefix with
  | nil R =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      exact ⟨_, R, [], [], rfl, rfl, StepPrefix.nil R,
        StepPrefix.nil R, rfl, rfl, by simp [traceBitCost]⟩
  | cons R Rnext i z tail hindex hguard hvertex hbody hbits hfixed htail ih =>
      intro j hj
      cases j with
      | zero =>
          exact ⟨_, R, [], z :: tail, rfl, rfl,
            StepPrefix.nil R,
            StepPrefix.cons R Rnext i z tail hindex hguard hvertex hbody
              hbits hfixed htail,
            rfl, rfl, by simp [traceBitCost]⟩
      | succ j =>
          obtain ⟨Wmid, Rmid, pref, suffix, heq, hlen,
            hpref, hsuffix, hrep, hrest, hbitsPref⟩ :=
              ih j (by simpa using hj)
          refine ⟨Wmid, Rmid, z :: pref, suffix, ?_, ?_, ?_, hsuffix,
            ?_, ?_, ?_⟩
          · simp [heq]
          · simp [hlen]
          · exact StepPrefix.cons R Rnext i z pref hindex hguard hvertex
              hbody hbits hfixed hpref
          · exact hrep.trans hfixed.2.1
          · exact hrest.trans hfixed.2.2.2.2.2.1
          · rw [hbitsPref, hfixed.2.1, hbits]
            simp [traceBitCost, ExecutedException.bitCost, List.drop_drop,
              Nat.add_comm, Nat.add_assoc]

lemma StepPrefix.head_guard
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {z : ExecutedException} {tail : List ExecutedException}
    (hprefix : StepPrefix R σfinal (z :: tail)) :
    (Cond.lt (.var "exceptionIndex")
      (.var "exceptionStop")).evalB B R.σ = some true := by
  cases hprefix with
  | cons R Rnext i z tail hindex hguard hvertex hbody hbits hfixed htail =>
      exact hguard

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
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace hfailedStop htail ih =>
      obtain ⟨K, hrun⟩ := hbody
      obtain ⟨L, htailRun⟩ := ih
      exact ⟨K + L, by
        simpa [repeatRepairBody, List.length_cons, Nat.add_assoc] using
          hrun.seq htailRun⟩

lemma StepChain.toPrefix
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps) :
    StepPrefix R σfinal steps := by
  induction hchain with
  | nil R hguard => exact StepPrefix.nil R
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace hfailedStop htail ih =>
      exact StepPrefix.cons R Rnext i z tail hindex hguard hvertex hbody
        hbits hfixed ih

lemma StepChain.end_guard_false
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps) :
    (Cond.lt (.var "exceptionIndex") (.var "exceptionStop")).evalB B
      σfinal = some false := by
  induction hchain with
  | nil R hguard => exact hguard
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace hfailedStop htail ih => exact ih

lemma traceBitCost_append_le {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (rep : ℕ → ℕ)
    (pref suffix : List ExecutedException) :
    traceBitCost G A rep pref ≤ traceBitCost G A rep (pref ++ suffix) := by
  simp only [traceBitCost, List.map_append, List.sum_append]
  omega

lemma guard_same_noninput {B : ℕ} {σ τ : Env}
    (hvars : σ.vars = τ.vars) :
    (Cond.lt (.var "exceptionIndex") (.var "exceptionStop")).evalB B σ =
      (Cond.lt (.var "exceptionIndex") (.var "exceptionStop")).evalB B τ := by
  cases σ with
  | mk vs arrs inp out =>
      cases τ with
      | mk ws arrs' inp' out' =>
          cases hvars
          rfl

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
      Rmid.bits = R.bits.drop (traceBitCost G A R.rep pref) ∧
      Rmid.exceptionList = R.exceptionList := by
  induction hchain with
  | nil R hguard =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      exact ⟨_, R, [], [], rfl, rfl, StepPrefix.nil R,
        StepChain.nil R hguard, rfl, rfl, by simp [traceBitCost], rfl⟩
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace hfailedStop htail ih =>
      intro j hj
      cases j with
      | zero =>
          exact ⟨_, R, [], z :: tail, rfl, rfl,
            StepPrefix.nil R,
            StepChain.cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits
              hfixed hfar hfailedFar hfailureTrace hfailedStop htail,
            rfl, rfl, by simp [traceBitCost], rfl⟩
      | succ j =>
          obtain ⟨Wmid, Rmid, pref, suffix, heq, hlen,
            hpref, hsuffix, hrep, hrest, hbitsPref, hlist⟩ :=
            ih j (by simpa using hj)
          refine ⟨Wmid, Rmid, z :: pref, suffix, ?_, ?_, ?_, hsuffix,
            ?_, ?_, ?_, ?_⟩
          · simp [heq]
          · simp [hlen]
          · exact StepPrefix.cons R Rnext i z pref hindex hguard hvertex hbody
              hbits hfixed hpref
          · exact hrep.trans hfixed.2.1
          · exact hrest.trans hfixed.2.2.2.2.2.1
          · rw [hbitsPref, hfixed.2.1, hbits]
            simp [traceBitCost, ExecutedException.bitCost, List.drop_drop,
              Nat.add_comm, Nat.add_assoc]
          · exact hlist.trans hfixed.1

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

/-- A completion with the same observed prefix cannot stop before the
reference completion: at the first alleged early stop its guard would be
both true and false in the same non-input state. -/
lemma StepChain.no_shorter_same_prefix
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (bits other : List Bool)
    {σρ στ : Env} {stepsρ stepsτ : List ExecutedException}
    (hchainρ : StepChain (R.reinput bits) σρ stepsρ)
    (hchainτ : StepChain (R.reinput other) στ stepsτ)
    (hboundρ : traceBitCost G A R.rep stepsρ ≤ other.length)
    (hboundτ : traceBitCost G A R.rep stepsτ ≤ other.length)
    (hprefix : bits.take (traceBitCost G A R.rep stepsρ) =
      other.take (traceBitCost G A R.rep stepsρ)) :
    stepsρ.length ≤ stepsτ.length := by
  by_contra hlt
  have hl : stepsτ.length ≤ stepsρ.length := by omega
  obtain ⟨Wρ, Pρ, prefρ, suffixρ, heqρ, hlenρ, hprefρ,
    hsuffixρ, _, hrestρ, hbitsρ, _⟩ :=
      StepChain.split_at hchainρ stepsτ.length hl
  obtain ⟨Wτ, Pτ, prefτ, suffixτ, heqτ, hlenτ, hprefτ,
    hsuffixτ, _, hrestτ, hbitsτ, _⟩ :=
      StepChain.split_at hchainτ stepsτ.length le_rfl
  have hdle : traceBitCost G A R.rep prefρ ≤
      traceBitCost G A R.rep stepsρ := by
    rw [heqρ]
    exact traceBitCost_append_le G A R.rep prefρ suffixρ
  have hboundρ' : traceBitCost G A R.rep prefρ ≤ other.length :=
    hdle.trans hboundρ
  have hboundτ' : traceBitCost G A R.rep prefτ ≤ other.length := by
    have hsufnil : suffixτ = [] := by
      have hlen := congrArg List.length heqτ
      simp only [List.length_append] at hlen
      have : suffixτ.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    subst suffixτ
    simpa [heqτ] using hboundτ
  have hprefix' : bits.take (traceBitCost G A R.rep prefρ) =
      other.take (traceBitCost G A R.rep prefρ) := by
    have hh := congrArg (List.take (traceBitCost G A R.rep prefρ)) hprefix
    simpa [List.take_take, Nat.min_eq_left hdle] using hh
  have hrepρ : (R.reinput bits).rep = R.rep := rfl
  have hrepτ : (R.reinput other).rep = R.rep := rfl
  have hstate := StepChain.prefix_replay R bits other Pρ Pτ prefρ prefτ
    hprefρ hprefτ hlenρ hlenτ (by simpa [LoopInput.reinput] using hrestρ)
    (by simpa [LoopInput.reinput] using hrestτ)
    (by simpa [LoopInput.reinput] using hbitsρ)
    (by simpa [LoopInput.reinput] using hbitsτ)
    hboundρ' hboundτ' hprefix'
  have hvars : Pρ.σ.vars = Pτ.σ.vars := by
    rw [hstate.2]
  have hguardEq := guard_same_noninput (B := B) hvars
  have hsufρne : suffixρ ≠ [] := by
    intro hz
    subst suffixρ
    have hh := congrArg List.length heqρ
    simp only [List.length_append, List.length_nil, Nat.add_zero] at hh
    omega
  cases suffixρ with
  | nil => contradiction
  | cons z zs =>
      cases hsuffixρ with
      | cons P Pnext i z zs hindex hstop hguard hvertex hbody hbits hfixed hfar
          hfailedFar hfailureTrace hfailedStop htail =>
          have hfalse : (Cond.lt (.var "exceptionIndex")
              (.var "exceptionStop")).evalB B Pτ.σ = some false := by
            have hsufnil : suffixτ = [] := by
              have hlen := congrArg List.length heqτ
              simp only [List.length_append] at hlen
              have : suffixτ.length = 0 := by omega
              exact List.length_eq_zero_iff.mp this
            subst suffixτ
            cases hsuffixτ with
            | nil P => assumption
          rw [hguardEq, hfalse] at hguard
          contradiction

/-- A realized initial segment of `j` calls remains available on every tape
that shares the bits consumed by that segment. This is the causal existence
fact needed before conditioning on the `j`-th local selector. -/
lemma StepPrefix.no_early_complete
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart Wend : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (bits other : List Bool)
    (Pend : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wend)
    {στ : Env} {pref stepsτ : List ExecutedException}
    (hprefixChain : StepPrefix (R.reinput bits) Pend.σ pref)
    (hchainτ : StepChain (R.reinput other) στ stepsτ)
    (hrest : Pend.rest = R.rest)
    (hbits : Pend.bits = bits.drop (traceBitCost G A R.rep pref))
    (hboundρ : traceBitCost G A R.rep pref ≤ other.length)
    (hboundτ : traceBitCost G A R.rep stepsτ ≤ other.length)
    (hprefix : bits.take (traceBitCost G A R.rep pref) =
      other.take (traceBitCost G A R.rep pref)) :
    pref.length ≤ stepsτ.length := by
  by_contra hlt
  have hl : stepsτ.length ≤ pref.length := by omega
  obtain ⟨Wρ, Pρ, prefρ, suffixρ, heqρ, hlenρ, hprefρ,
    hsuffixρ, _, hrestρ, hbitsρ⟩ :=
      StepPrefix.split_at hprefixChain stepsτ.length hl
  obtain ⟨Wτ, Pτ, prefτ, suffixτ, heqτ, hlenτ, hprefτ,
    hsuffixτ, _, hrestτ, hbitsτ, _⟩ :=
      StepChain.split_at hchainτ stepsτ.length le_rfl
  have hdle : traceBitCost G A R.rep prefρ ≤
      traceBitCost G A R.rep pref := by
    rw [heqρ]
    exact traceBitCost_append_le G A R.rep prefρ suffixρ
  have hboundρ' : traceBitCost G A R.rep prefρ ≤ other.length :=
    hdle.trans hboundρ
  have hboundτ' : traceBitCost G A R.rep prefτ ≤ other.length := by
    have hsufnil : suffixτ = [] := by
      have hlen := congrArg List.length heqτ
      simp only [List.length_append] at hlen
      have : suffixτ.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    subst suffixτ
    simpa [heqτ] using hboundτ
  have hprefix' : bits.take (traceBitCost G A R.rep prefρ) =
      other.take (traceBitCost G A R.rep prefρ) := by
    have hh := congrArg (List.take (traceBitCost G A R.rep prefρ)) hprefix
    simpa [List.take_take, Nat.min_eq_left hdle] using hh
  have hstate := StepChain.prefix_replay R bits other Pρ Pτ prefρ prefτ
    hprefρ hprefτ hlenρ hlenτ
    (by simpa [LoopInput.reinput] using hrestρ)
    (by simpa [LoopInput.reinput] using hrestτ)
    (by simpa [LoopInput.reinput] using hbitsρ)
    (by simpa [LoopInput.reinput] using hbitsτ)
    hboundρ' hboundτ' hprefix'
  have hvars : Pρ.σ.vars = Pτ.σ.vars := by rw [hstate.2]
  have hguardEq := guard_same_noninput (B := B) hvars
  have hsufρne : suffixρ ≠ [] := by
    intro hz
    subst suffixρ
    have hh := congrArg List.length heqρ
    simp only [List.length_append, List.length_nil, Nat.add_zero] at hh
    omega
  cases suffixρ with
  | nil => contradiction
  | cons z zs =>
      have hguard := StepPrefix.head_guard hsuffixρ
      have hfalse : (Cond.lt (.var "exceptionIndex")
          (.var "exceptionStop")).evalB B Pτ.σ = some false := by
        have hsufnil : suffixτ = [] := by
          have hlen := congrArg List.length heqτ
          simp only [List.length_append] at hlen
          have : suffixτ.length = 0 := by omega
          exact List.length_eq_zero_iff.mp this
        subst suffixτ
        cases hsuffixτ with
        | nil P => assumption
      rw [hguardEq, hfalse] at hguard
      contradiction

/-- Once a local retry reports failure, the actual repair loop has no
subsequent body call: its stop index is already the current index. -/
lemma StepChain.nil_of_guard_false
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps)
    (hfalse : (Cond.lt (.var "exceptionIndex")
      (.var "exceptionStop")).evalB B R.σ = some false) :
    steps = [] ∧ σfinal = R.σ := by
  cases hchain with
  | nil => exact ⟨rfl, rfl⟩
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace hfailedStop htail =>
      rw [hfalse] at hguard
      contradiction

/-- The source failure certificate belongs to the last actual exception
call, with every earlier call captured in chronological order. -/
lemma StepChain.failed_final_step
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
    ∃ pref z, steps = pref ++ [z] ∧
      ∃ (W Wnext : Finset ℕ)
        (Rcur : LoopInput B n s t bufferCap targetCap q cap k e
          G x E groupedB Wbase A W)
        (Rnext : LoopInput B n s t bufferCap targetCap q cap k e
          G x E groupedB Wbase A Wnext)
        (i : ℕ),
        z.vertex = Rcur.exceptionList i ∧
        FarStepTrace Rcur i z.attempts z.used ∧
        FarStepFailureTrace Rcur i z.attempts z.used
          (Rnext.σ.vars "repairRetryStatus") ∧
        (Rnext.σ.vars "repairRetryStatus" = 2 ∨
          Rnext.σ.vars "repairRetryStatus" = 3) ∧
        σfinal = Rnext.σ := by
  induction hchain with
  | nil R hguard =>
      rcases hfinal with h2 | h3
      · exact False.elim (hstart.1 h2)
      · exact False.elim (hstart.2 h3)
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed hfar
      hfailedFar hfailureTrace hfailedStop htail ih =>
      by_cases hf : Rnext.σ.vars "repairRetryStatus" = 2 ∨
        Rnext.σ.vars "repairRetryStatus" = 3
      · obtain ⟨htailNil, hfinalEq⟩ :=
          StepChain.nil_of_guard_false htail (hfailedStop hf)
        subst tail
        refine ⟨[], z, rfl, _, _, R, Rnext, i,
          hvertex, hfar (hfailedFar hf), hfailureTrace hf, hf, ?_⟩
        exact hfinalEq
      · obtain ⟨pref, z', heq, W, Wnext', Rcur, Rnext', j,
          hz', hfar', htrace', hf', hfinalEq⟩ :=
            ih ⟨by tauto, by tauto⟩ hfinal
        exact ⟨z :: pref, z', by simp [heq], W, Wnext', Rcur,
          Rnext', j, hz', hfar', htrace', hf', hfinalEq⟩

/-- A completed exception loop is fully determined through its consumed
prefix: every other completion sharing that prefix has the same call count
and non-input final state. -/
lemma StepChain.same_result_same_prefix
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (bits other : List Bool)
    {σρ στ : Env} {stepsρ stepsτ : List ExecutedException}
    (hchainρ : StepChain (R.reinput bits) σρ stepsρ)
    (hchainτ : StepChain (R.reinput other) στ stepsτ)
    (hboundρ : traceBitCost G A R.rep stepsρ ≤ other.length)
    (hboundτ : traceBitCost G A R.rep stepsτ ≤ other.length)
    (hprefix : bits.take (traceBitCost G A R.rep stepsρ) =
      other.take (traceBitCost G A R.rep stepsρ)) :
    stepsτ.length = stepsρ.length ∧
      στ = {σρ with inp :=
        (other.drop (traceBitCost G A R.rep stepsρ)).map Bool.toNat ++
          R.rest} := by
  have hle := StepChain.no_shorter_same_prefix R bits other hchainρ
    hchainτ hboundρ hboundτ hprefix
  obtain ⟨Wρ, Pρ, prefρ, suffixρ, heqρ, hlenρ, hprefρ,
    hsuffixρ, _, hrestρ, hbitsρ, _⟩ :=
      StepChain.split_at hchainρ stepsρ.length le_rfl
  obtain ⟨Wτ, Pτ, prefτ, suffixτ, heqτ, hlenτ, hprefτ,
    hsuffixτ, _, hrestτ, hbitsτ, _⟩ :=
      StepChain.split_at hchainτ stepsρ.length hle
  have hsufρnil : suffixρ = [] := by
    have hlen := congrArg List.length heqρ
    simp only [List.length_append] at hlen
    have : suffixρ.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  subst suffixρ
  have hprefρeq : prefρ = stepsρ := by simpa using heqρ.symm
  subst prefρ
  have hboundτ' : traceBitCost G A R.rep prefτ ≤ other.length := by
    have hle' : traceBitCost G A R.rep prefτ ≤
        traceBitCost G A R.rep stepsτ := by
      rw [heqτ]
      exact traceBitCost_append_le G A R.rep prefτ suffixτ
    exact hle'.trans hboundτ
  have hstate := StepChain.prefix_replay R bits other Pρ Pτ stepsρ prefτ
    hprefρ hprefτ hlenρ hlenτ (by simpa [LoopInput.reinput] using hrestρ)
    (by simpa [LoopInput.reinput] using hrestτ)
    (by simpa [LoopInput.reinput] using hbitsρ)
    (by simpa [LoopInput.reinput] using hbitsτ)
    hboundρ hboundτ' hprefix
  have hguardρ : (Cond.lt (.var "exceptionIndex")
      (.var "exceptionStop")).evalB B Pρ.σ = some false := by
    cases hsuffixρ with
    | nil P => assumption
  have hguardτ : (Cond.lt (.var "exceptionIndex")
      (.var "exceptionStop")).evalB B Pτ.σ = some false := by
    have hvars : Pρ.σ.vars = Pτ.σ.vars := by rw [hstate.2]
    rw [← guard_same_noninput (B := B) hvars]
    exact hguardρ
  have hsufτnil : suffixτ = [] := by
    cases suffixτ with
    | nil => rfl
    | cons z zs =>
        cases hsuffixτ with
        | cons P Pnext i z zs hindex hstop hguard hvertex hbody hbits hfixed
            hfar hfailedFar hfailureTrace hfailedStop htail =>
            rw [hguardτ] at hguard
            contradiction
  subst suffixτ
  have hlenEq : stepsτ.length = stepsρ.length := by
    have hh := congrArg List.length heqτ
    simp only [List.length_append, List.length_nil, Nat.add_zero] at hh
    omega
  have hσρ : σρ = Pρ.σ := by
    cases hsuffixρ with
    | nil P => rfl
  have hστ : στ = Pτ.σ := by
    cases hsuffixτ with
    | nil P => rfl
  refine ⟨hlenEq, ?_⟩
  rw [hσρ, hστ]
  exact hstate.2

/-- The first `j` calls of a completed source chain form a replayable prefix. -/
lemma StepChain.stage_prefix
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps) (j : ℕ)
    (hj : j ≤ steps.length) :
    ∃ (Wmid : Finset ℕ)
      (Rmid : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wmid),
      StepPrefix R Rmid.σ (steps.take j) ∧
      Rmid.rest = R.rest ∧
      Rmid.bits = R.bits.drop
        (traceBitCost G A R.rep (steps.take j)) := by
  obtain ⟨Wmid, Rmid, pref, suffix, heq, hlen, hpref, _, _, hrest,
    hbits, _⟩ := StepChain.split_at hchain j hj
  have hprefEq : pref = steps.take j := by
    rw [heq]
    simp [hlen]
  subst pref
  exact ⟨Wmid, Rmid, hpref, hrest, hbits⟩

/-- Split a completed chain at a chronological call index, retaining both
the replayable prefix and its actual continuation. -/
lemma StepChain.stage_split
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps) (j : ℕ)
    (hj : j ≤ steps.length) :
    ∃ (Wmid : Finset ℕ)
      (Rmid : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wmid),
      StepPrefix R Rmid.σ (steps.take j) ∧
      StepChain Rmid σfinal (steps.drop j) ∧
      Rmid.rep = R.rep ∧ Rmid.exceptionList = R.exceptionList ∧
      Rmid.rest = R.rest ∧
      Rmid.bits = R.bits.drop
        (traceBitCost G A R.rep (steps.take j)) := by
  obtain ⟨Wmid, Rmid, pref, suffix, heq, hlen, hpref, hsuffix,
    hrep, hrest, hbits, hlist⟩ := StepChain.split_at hchain j hj
  have hprefEq : pref = steps.take j := by
    rw [heq]
    simp [hlen]
  have hsuffixEq : suffix = steps.drop j := by
    rw [heq]
    simp [hlen]
  subst pref
  subst suffix
  exact ⟨Wmid, Rmid, hpref, hsuffix, hrep, hlist, hrest, hbits⟩

/-- A failed completion of length `j + 1` is witnessed by the actual body
call immediately after its first `j` calls. -/
lemma StepChain.failed_at_stage
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps)
    (j status : ℕ) (hlen : steps.length = j + 1)
    (hstatus : σfinal.vars "repairRetryStatus" = status)
    (hfailed : status = 2 ∨ status = 3) :
    ∃ (W Wnext : Finset ℕ)
      (Rcur : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A W)
      (Rnext : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wnext)
      (i : ℕ) (z : ExecutedException),
      StepPrefix R Rcur.σ (steps.take j) ∧
      steps.drop j = [z] ∧
      Rcur.rest = R.rest ∧
      Rcur.bits = R.bits.drop
        (traceBitCost G A R.rep (steps.take j)) ∧
      (∃ K, Run B exceptionRepairBody Rcur.σ Rnext.σ K) ∧
      z.vertex = Rcur.exceptionList i ∧
      FarStepTrace Rcur i z.attempts z.used ∧
      FarStepFailureTrace Rcur i z.attempts z.used status ∧
      Rnext.σ = σfinal := by
  have hj : j ≤ steps.length := by omega
  obtain ⟨W, Rcur, hpref, hsuffix, _, _, hrest, hbitsCur⟩ :=
    StepChain.stage_split hchain j hj
  have htailLength : (steps.drop j).length = 1 := by
    simp [List.length_drop, hlen]
  generalize hz : steps.drop j = suffix at hsuffix htailLength ⊢
  cases hsuffix with
  | nil Rcur hguard => simp at htailLength
  | cons Rcur Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed
      hfar hfailedFar hfailureTrace hfailedStop htail =>
      have htailNil : tail = [] := by
        simp at htailLength
        exact htailLength
      subst tail
      cases htail with
      | nil Rnext hguardFalse =>
          have hf : Rnext.σ.vars "repairRetryStatus" = 2 ∨
              Rnext.σ.vars "repairRetryStatus" = 3 := by
            simpa [← hstatus] using hfailed
          refine ⟨_, _, Rcur, Rnext, i, z, hpref, rfl, hrest,
            hbitsCur, hbody, hvertex, hfar (hfailedFar hf), ?_, rfl⟩
          simpa [← hstatus] using hfailureTrace hf

/-- The first actual call of a nonempty chain still has the original stop
index, so its packed index lies below the exception count. -/
lemma StepChain.head_ready
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    {R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart}
    {σfinal : Env} {steps : List ExecutedException}
    (hchain : StepChain R σfinal steps) (hne : steps ≠ []) :
    ∃ i, R.σ.vars "exceptionIndex" = i ∧
      R.σ.vars "exceptionStop" = e ∧ i < e := by
  cases hchain with
  | nil => contradiction
  | cons R Rnext i z tail hindex hstop hguard hvertex hbody hbits hfixed
      hfar hfailedFar hfailureTrace hfailedStop htail =>
      refine ⟨i, hindex, hstop, ?_⟩
      obtain ⟨a, b, ha, hb, he⟩ := evalB_condLt_iff.mp hguard
      obtain ⟨rfl, _⟩ := evalB_var_iff.mp ha
      obtain ⟨rfl, _⟩ := evalB_var_iff.mp hb
      simpa [hindex, hstop] using he

/-- At any reached call index, the consumed prefix and the prepared
pre-call state replay on every tape sharing that prefix. -/
lemma StepChain.stage_replay
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (bits other : List Bool)
    {σρ στ : Env} {stepsρ stepsτ : List ExecutedException}
    (hchainρ : StepChain (R.reinput bits) σρ stepsρ)
    (hchainτ : StepChain (R.reinput other) στ stepsτ)
    (j : ℕ) (hjρ : j ≤ stepsρ.length)
    (hboundρ : traceBitCost G A R.rep stepsρ ≤ other.length)
    (hboundτ : traceBitCost G A R.rep stepsτ ≤ other.length)
    (hprefix : bits.take
      (traceBitCost G A R.rep (stepsρ.take j)) = other.take
        (traceBitCost G A R.rep (stepsρ.take j))) :
    j ≤ stepsτ.length ∧
      traceBitCost G A R.rep (stepsτ.take j) =
        traceBitCost G A R.rep (stepsρ.take j) ∧
      ∃ (Wρ Wτ : Finset ℕ)
        (Pρ : LoopInput B n s t bufferCap targetCap q cap k e
          G x E groupedB Wbase A Wρ)
        (Pτ : LoopInput B n s t bufferCap targetCap q cap k e
          G x E groupedB Wbase A Wτ),
        StepPrefix (R.reinput bits) Pρ.σ (stepsρ.take j) ∧
        StepPrefix (R.reinput other) Pτ.σ (stepsτ.take j) ∧
        Pτ.σ = {Pρ.σ with inp :=
          (other.drop (traceBitCost G A R.rep (stepsρ.take j))).map Bool.toNat ++
            R.rest} := by
  obtain ⟨Wρ, Pρ, hprefρ, hrestρ, hbitsρ⟩ :=
    StepChain.stage_prefix hchainρ j hjρ
  have hcostρ : traceBitCost G A R.rep (stepsρ.take j) ≤
      traceBitCost G A R.rep stepsρ := by
    conv_rhs => rw [← List.take_append_drop j stepsρ]
    exact traceBitCost_append_le G A R.rep _ _
  have hboundρ' := hcostρ.trans hboundρ
  have hjτ : j ≤ stepsτ.length := by
    have hh := StepPrefix.no_early_complete R bits other Pρ hprefρ hchainτ
      (by simpa [LoopInput.reinput] using hrestρ)
      (by simpa [LoopInput.reinput] using hbitsρ)
      hboundρ' hboundτ hprefix
    simpa [List.length_take, Nat.min_eq_left hjρ] using hh
  obtain ⟨Wτ, Pτ, hprefτ, hrestτ, hbitsτ⟩ :=
    StepChain.stage_prefix hchainτ j hjτ
  have hcostτ : traceBitCost G A R.rep (stepsτ.take j) ≤
      traceBitCost G A R.rep stepsτ := by
    conv_rhs => rw [← List.take_append_drop j stepsτ]
    exact traceBitCost_append_le G A R.rep _ _
  have hstate := StepChain.prefix_replay (j := j) R bits other Pρ Pτ
    (stepsρ.take j) (stepsτ.take j) hprefρ hprefτ
    (by simp [List.length_take, Nat.min_eq_left hjρ])
    (by simp [List.length_take, Nat.min_eq_left hjτ])
    (by simpa [LoopInput.reinput] using hrestρ)
    (by simpa [LoopInput.reinput] using hrestτ)
    (by simpa [LoopInput.reinput] using hbitsρ)
    (by simpa [LoopInput.reinput] using hbitsτ)
    hboundρ' (hcostτ.trans hboundτ) hprefix
  exact ⟨hjτ, hstate.1, Wρ, Wτ, Pρ, Pτ, hprefρ,
    hprefτ, hstate.2⟩

/-- The amount consumed before call `j`, or before an earlier stop, is a
stopping time on the flat input tape. -/
lemma StepChain.stage_cost_causal
    {B n s t bufferCap targetCap q cap k e N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (steps : FlatTraceLaw.FlatTape N → List ExecutedException)
    (final : FlatTraceLaw.FlatTape N → Env)
    (hchain : ∀ ρ, StepChain
      (R.reinput (FlatTraceLaw.flatBits ρ)) (final ρ) (steps ρ))
    (hbound : ∀ ρ, traceBitCost G A R.rep (steps ρ) ≤ N)
    (j : ℕ) (ρ τ : FlatTraceLaw.FlatTape N)
    (hprefix : (FlatTraceLaw.flatBits ρ).take
      (traceBitCost G A R.rep ((steps ρ).take j)) =
      (FlatTraceLaw.flatBits τ).take
        (traceBitCost G A R.rep ((steps ρ).take j))) :
    traceBitCost G A R.rep ((steps τ).take j) =
      traceBitCost G A R.rep ((steps ρ).take j) := by
  by_cases hj : j ≤ (steps ρ).length
  · exact (StepChain.stage_replay R _ _ (hchain ρ) (hchain τ) j hj
      (by simpa [FlatTraceLaw.flatBits_length] using hbound ρ)
      (by simpa [FlatTraceLaw.flatBits_length] using hbound τ)
      hprefix).2.1
  · have hlenρ : (steps ρ).length ≤ j := by omega
    have hprefρ : (steps ρ).take j = steps ρ :=
      List.take_of_length_le hlenρ
    have hprefixFull : (FlatTraceLaw.flatBits ρ).take
        (traceBitCost G A R.rep (steps ρ)) =
        (FlatTraceLaw.flatBits τ).take
          (traceBitCost G A R.rep (steps ρ)) := by
      simpa only [hprefρ] using hprefix
    have hlen := (StepChain.same_result_same_prefix R _ _
      (hchain ρ) (hchain τ)
      (by simpa [FlatTraceLaw.flatBits_length] using hbound ρ)
      (by simpa [FlatTraceLaw.flatBits_length] using hbound τ)
      hprefixFull).1
    have hlenτ : (steps τ).length ≤ j := by omega
    have hcost := (StepChain.stage_replay R _ _
      (hchain ρ) (hchain τ) (steps ρ).length (le_refl _)
      (by simpa [FlatTraceLaw.flatBits_length] using hbound ρ)
      (by simpa [FlatTraceLaw.flatBits_length] using hbound τ)
      (by simpa only [List.take_of_length_le (le_refl (steps ρ).length)]
        using hprefixFull)).2.1
    simpa only [List.take_of_length_le hlenρ,
      List.take_of_length_le hlenτ,
      List.take_of_length_le (by omega : (steps τ).length ≤ (steps ρ).length),
      List.take_of_length_le (le_refl (steps ρ).length)] using hcost

/-- Every recorded prefix consumes at most one reserved segment per call. -/
lemma traceBitCost_take_le
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (steps : List ExecutedException)
    (hvalid : ∀ z ∈ steps,
      z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t))
    (j : ℕ) (hj : j ≤ steps.length) :
    traceBitCost G A R.rep (steps.take j) ≤
      j * (cap * (s * t * Nat.clog 2 n)) := by
  let C := cap * (s * t * Nat.clog 2 n)
  have hcost (z : ExecutedException) (hz : z ∈ steps) :
      z.bitCost G A R.rep ≤ C := by
    have hlog : Nat.clog 2
        (ExceptionRepairMean.farDomain G A R.rep z.vertex).card ≤
        Nat.clog 2 n := Nat.clog_mono_right 2
          (ExceptionLoopMean.far_card_le R z.vertex)
    have hu : z.used ≤ cap * (s * t) :=
      (hvalid z hz).2.trans
        (Nat.mul_le_mul_right (s * t) (hvalid z hz).1)
    calc
      z.bitCost G A R.rep = z.used * Nat.clog 2
          (ExceptionRepairMean.farDomain G A R.rep z.vertex).card := rfl
      _ ≤ (cap * (s * t)) * Nat.clog 2 n := by gcongr
      _ = C := by dsimp [C]; ring
  have hh : ((steps.take j).map (ExecutedException.bitCost G A R.rep)).sum ≤
      C * (steps.take j).length := by
    have hle := List.sum_le_card_nsmul
      ((steps.take j).map (ExecutedException.bitCost G A R.rep)) C (by
        intro d hd
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
        exact hcost z (List.mem_of_mem_take hz))
    simpa [List.length_map, nsmul_eq_mul, Nat.mul_comm] using hle
  simpa [traceBitCost, List.length_take, Nat.min_eq_left hj,
    Nat.mul_comm] using hh

/-- Count a rare event by its conditional count on every actual stopping
prefix. This finite form is used for each chronological exception call. -/
lemma count_le_of_stopped_fibers {N t c : ℕ}
    (used : FlatTraceLaw.FlatTape N → ℕ)
    (hbound : ∀ ρ, used ρ ≤ N)
    (hcausal : ∀ ρ τ,
      (FlatTraceLaw.flatBits ρ).take (used ρ) =
        (FlatTraceLaw.flatBits τ).take (used ρ) → used τ = used ρ)
    (event : FlatTraceLaw.FlatTape N → Prop) [DecidablePred event]
    (hfiber : ∀ ρ,
      2 ^ t * (Finset.univ.filter fun η : FlatTraceLaw.FlatTape
        (N - used ρ) =>
          event ((Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
            (hbound ρ)).symm
            ((Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
              (hbound ρ) ρ).1, η))).card ≤ c * 2 ^ (N - used ρ)) :
    2 ^ t * (Finset.univ.filter event).card ≤ c * 2 ^ N := by
  classical
  open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting in
  let X (ρ : FlatTraceLaw.FlatTape N) : ℚ := if event ρ then 1 else 0
  let Y (_ : FlatTraceLaw.FlatTape N) : ℚ := (c : ℚ) / 2 ^ t
  have hmean := StoppedPrefixAveraging.sum_le_of_stopped_prefix used hbound
    (by simpa only [FlatTraceLaw.flatBits] using hcausal)
    X Y (by intros; rfl) (by
      intro ρ
      let f (η : FlatTraceLaw.FlatTape (N - used ρ)) :=
        (Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
          (hbound ρ)).symm
          ((Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
            (hbound ρ) ρ).1, η)
      let bad := (Finset.univ : Finset (FlatTraceLaw.FlatTape (N - used ρ))).filter
        (fun η => event (f η))
      have hsum : (∑ η : FlatTraceLaw.FlatTape (N - used ρ), X (f η)) =
          (bad.card : ℚ) := by
        rw [Finset.card_filter]
        push_cast
        rfl
      rw [hsum]
      have hNat : 2 ^ t * bad.card ≤ c * 2 ^ (N - used ρ) := by
        simpa only [bad, f] using hfiber ρ
      have hQ : (2 ^ t : ℚ) * (bad.card : ℚ) ≤
          (c : ℚ) * 2 ^ (N - used ρ) := by exact_mod_cast hNat
      dsimp [Y]
      have hh : (bad.card : ℚ) ≤
          ((c : ℚ) * 2 ^ (N - used ρ)) / 2 ^ t :=
        (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ t)).2 (by
          simpa [mul_comm] using hQ)
      convert hh using 1 <;> ring)
  have hsumX : (∑ ρ : FlatTraceLaw.FlatTape N, X ρ) =
      ((Finset.univ.filter event).card : ℚ) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hsumY : (∑ _ρ : FlatTraceLaw.FlatTape N, Y _ρ) =
      (c : ℚ) * 2 ^ N / 2 ^ t := by
    simp [Y, Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.card_tape]
    ring
  rw [hsumX, hsumY] at hmean
  have hQ : (2 ^ t : ℚ) * ((Finset.univ.filter event).card : ℚ) ≤
      (c : ℚ) * 2 ^ N := by
    have hh := (le_div_iff₀
      (by positivity : (0 : ℚ) < 2 ^ t)).mp hmean
    simpa [mul_comm] using hh
  exact_mod_cast hQ

/-- An abort has a unique final call index, so the per-call counts add with
one factor for the number of packed exceptions. -/
lemma count_le_of_final_stage {N e t c : ℕ}
    (steps : FlatTraceLaw.FlatTape N → List ExecutedException)
    (event : FlatTraceLaw.FlatTape N → Prop) [DecidablePred event]
    (hlength : ∀ ρ, event ρ →
      0 < (steps ρ).length ∧ (steps ρ).length ≤ e)
    (hstage : ∀ j < e,
      2 ^ t * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
        event ρ ∧ (steps ρ).length = j + 1).card ≤ c * 2 ^ N) :
    2 ^ t * (Finset.univ.filter event).card ≤ e * c * 2 ^ N := by
  classical
  let stage (j : ℕ) :=
    (Finset.univ : Finset (FlatTraceLaw.FlatTape N)).filter
      (fun ρ => event ρ ∧ (steps ρ).length = j + 1)
  have hcover : (Finset.univ.filter event : Finset (FlatTraceLaw.FlatTape N)) =
      (Finset.range e).biUnion stage := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, stage]
    constructor
    · intro he
      obtain ⟨hpos, hle⟩ := hlength ρ he
      exact ⟨(steps ρ).length - 1, by omega, he, by omega⟩
    · rintro ⟨j, _, he, _⟩
      exact he
  have hdisjoint : ((Finset.range e : Finset ℕ) : Set ℕ).PairwiseDisjoint stage := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro ρ hρi hρj
    have hi' := (Finset.mem_filter.mp hρi).2.2
    have hj' := (Finset.mem_filter.mp hρj).2.2
    omega
  rw [hcover, Finset.card_biUnion hdisjoint, Finset.mul_sum]
  calc
    ∑ j ∈ Finset.range e, 2 ^ t * (stage j).card ≤
        ∑ _j ∈ Finset.range e, c * 2 ^ N := by
      apply Finset.sum_le_sum
      intro j hj
      exact hstage j (Finset.mem_range.mp hj)
    _ = e * c * 2 ^ N := by simp [mul_assoc]

/-- A source call with its physical failure certificate, sharing the
runtime record used by the stopped-prefix mean proof. -/
structure FailureStepRecord
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent) (i : ℕ) where
  step : ExceptionLoopMean.StepRecord R i
  failedFar : (step.next.σ.vars "repairRetryStatus" = 2 ∨
      step.next.σ.vars "repairRetryStatus" = 3) →
    (2 * k) / 3 <
      (ExceptionRepairMean.farDomain G A R.rep (R.exceptionList i)).card
  failure : (step.next.σ.vars "repairRetryStatus" = 2 ∨
      step.next.σ.vars "repairRetryStatus" = 3) →
    FarStepFailureTrace R i step.attempts step.used
      (step.next.σ.vars "repairRetryStatus")

lemma failureStepRecord_exists
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (i : ℕ) (hindex : R.σ.vars "exceptionIndex" = i)
    (hstop : R.σ.vars "exceptionStop" = e) (hi : i < e)
    (hb : cap * (s * t * Nat.clog 2
      (ExceptionRepairMean.farDomain G A R.rep (R.exceptionList i)).card) ≤
        R.bits.length) : Nonempty (FailureStepRecord R i) := by
  obtain ⟨Wnext, Rnext, attempts, used, charge, rbody, hcharge,
    hattempts, hused, hbits, hfixed, hout, hfar,
    hfailedFar, hfailure⟩ :=
      one_step_run_trace R hindex hstop hi (by simpa [ExceptionRepairMean.farDomain] using hb)
  let S : ExceptionLoopMean.StepRecord R i := {
    Wnext := Wnext
    next := Rnext
    attempts := attempts
    used := used
    bodyCost := charge + if Rnext.σ.vars "repairRetryStatus" = 1 then 11 else 9
    run := rbody
    bound := by rw [hcharge]; split_ifs <;> omega
    attempts_le := hattempts
    used_le := hused
    bits := by simpa [ExceptionRepairMean.farDomain] using hbits
    fixed := hfixed
    outcome := by
      rcases hout with hs | hf
      · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1⟩
      · exact Or.inr ⟨hf.1, hf.2.1, hf.2.2.1⟩
    far := by simpa [ExceptionRepairMean.farDomain] using hfar
  }
  refine ⟨⟨S, ?_, ?_⟩⟩
  · simpa [S, ExceptionRepairMean.farDomain] using hfailedFar
  · simpa [S] using hfailure

/-- Fixed-stage selector and retry exhaustion counts for the actual prepared
local inputs. Only occupied domain cells matter, so framing unused cells is
harmless. The outer stopped-prefix argument supplies this common stage. -/
lemma fixed_prepared_failure_counts
    {B n m s t bufferCap targetCap q b cap N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (P : FlatTraceLaw.FlatTape N →
      ReadyInput B n m n s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (base : FlatTraceLaw.FlatTape N)
    (hbits : ∀ ρ, (P ρ).bits = FlatTraceLaw.flatBits ρ)
    (hdomain : ∀ ρ j, j < m → (P ρ).domain j = (P base).domain j)
    (hhalf : 2 * (LocalFlatLaw.localBadOutputs m s (P base).domain
      (numericNeighborhood G) groupedB Wbase b).card ≤ m ^ s)
    (hselectorBudget : cap * s * t * Nat.clog 2 m ≤ N)
    (hretryBudget : cap * ClassRepresentativeTrace.bitBudget
      (fun _ => m) t 0 s ≤ N)
    (status2 status3 : FlatTraceLaw.FlatTape N → Prop)
    [DecidablePred status2] [DecidablePred status3]
    (hstatus2 : ∀ ρ, status2 ρ → ∃ attempts, attempts ≤ cap ∧
      LocalRepairRetriesSource.FlatSelectorFailed m (P ρ).hpositive t s
        (LocalFlatLaw.localBadOutputs m s (P ρ).domain
          (numericNeighborhood G) groupedB Wbase b)
        attempts (P ρ).bits)
    (hstatus3 : ∀ ρ, status3 ρ →
      LocalFlatLaw.FlatRejectedTrials m t s
        (LocalFlatLaw.localBadOutputs m s (P ρ).domain
          (numericNeighborhood G) groupedB Wbase b)
        cap (P ρ).bits) :
    2 ^ t * (Finset.univ.filter status2).card ≤ cap * s * 2 ^ N ∧
    2 ^ cap * (Finset.univ.filter status3).card ≤ 2 ^ N := by
  classical
  let bad := LocalFlatLaw.localBadOutputs m s (P base).domain
    (numericNeighborhood G) groupedB Wbase b
  have hbad (ρ : FlatTraceLaw.FlatTape N) :
      LocalFlatLaw.localBadOutputs m s (P ρ).domain
        (numericNeighborhood G) groupedB Wbase b = bad := by
    exact LocalSelectorAbort.localBadOutputs_congr_domain m s
      (P ρ).domain (P base).domain (numericNeighborhood G)
      groupedB Wbase b (hdomain ρ)
  have hvalid : bad ⊆ FlatTraceLaw.outputVectors (fun _ => m)
      (fun _ => 0) 0 s := by
    intro output ho
    exact (Finset.mem_filter.mp ho).1
  constructor
  · apply LocalSelectorAbort.selector_failure_count_le m t s cap N bad
      (P base).hpositive hselectorBudget status2
    intro ρ hf
    obtain ⟨attempts, ha, htrace⟩ := hstatus2 ρ hf
    refine ⟨attempts, ha, ?_⟩
    simpa only [hbad ρ, hbits ρ] using htrace
  · apply ExceptionRepairMean.actual_exhaustion_count_le m t s cap N bad
      hvalid (by simpa only [bad, LocalFlatLaw.local_outputCount] using hhalf)
      hretryBudget status3
    intro ρ hf
    simpa only [hbad ρ, hbits ρ] using hstatus3 ρ hf

/-- Each actual source call has selector failure mass at most `cap*s/2^t`
and retry exhaustion mass at most `1/2^cap`, on the same finite tape. -/
lemma one_step_failure_counts
    {B n s t bufferCap targetCap q cap k e N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (i : ℕ) (hindex : R.σ.vars "exceptionIndex" = i)
    (hstop : R.σ.vars "exceptionStop" = e) (hi : i < e)
    (hbudget : cap * (s * t * Nat.clog 2 n) ≤ N)
    (hhalf : (2 * k) / 3 <
      (ExceptionRepairMean.farDomain G A R.rep (R.exceptionList i)).card →
        2 * (SamplerLocalSuccess.localTrialFailureSet
          (numericNeighborhood G) groupedB Wbase (R.exceptionList i)
          (ExceptionRepairMean.farDomain G A R.rep (R.exceptionList i)) s).card ≤
          (ExceptionRepairMean.farDomain G A R.rep (R.exceptionList i)).card ^ s)
    (F : ∀ ρ : FlatTraceLaw.FlatTape N,
      FailureStepRecord (R.reinput (FlatTraceLaw.flatBits ρ)) i) :
    2 ^ t * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
      (F ρ).step.next.σ.vars "repairRetryStatus" = 2).card ≤
        cap * s * 2 ^ N ∧
    2 ^ cap * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
      (F ρ).step.next.σ.vars "repairRetryStatus" = 3).card ≤
        2 ^ N := by
  classical
  let b := R.exceptionList i
  let X := ExceptionRepairMean.farDomain G A R.rep b
  by_cases hfar : (2 * k) / 3 < X.card
  · let hFar (ρ : FlatTraceLaw.FlatTape N) :
        FarStepTrace (R.reinput (FlatTraceLaw.flatBits ρ)) i
          (F ρ).step.attempts (F ρ).step.used :=
      (F ρ).step.far (by simpa [X, b, LoopInput.reinput] using hfar)
    let P (ρ : FlatTraceLaw.FlatTape N) := Classical.choose (hFar ρ)
    have hP (ρ : FlatTraceLaw.FlatTape N) := Classical.choose_spec (hFar ρ)
    have hbits (ρ : FlatTraceLaw.FlatTape N) :
        (P ρ).bits = FlatTraceLaw.flatBits ρ := (hP ρ).2.1
    have hrest (ρ : FlatTraceLaw.FlatTape N) :
        (P ρ).rest = R.rest := (hP ρ).2.2.1
    have hprep (ρ : FlatTraceLaw.FlatTape N) :
        Run B ((Com.assign "repairB"
          (.get "exceptionList" (.var "exceptionIndex"))).seq
          RepairFilterSource.repairDomainSource)
          (R.reinput (FlatTraceLaw.flatBits ρ)).σ (P ρ).σ
          (3 + domainCharge x G A R.rep b) := (hP ρ).1
    have hXn : X.card ≤ n := ExceptionLoopMean.far_card_le R b
    have hdomain (ρ : FlatTraceLaw.FlatTape N) (j : ℕ)
        (hj : j < X.card) : (P ρ).domain j = (P (fun _ => false)).domain j := by
      have hh := ExceptionRepairMean.prepared_same_reinputs R
        (FlatTraceLaw.flatBits ρ)
        (FlatTraceLaw.flatBits (fun _ : Fin N => false))
        (P ρ) (P (fun _ => false)) (hbits ρ) (hrest ρ)
        (hprep ρ) (hprep (fun _ => false))
      exact hh.2 j (hj.trans_le hXn)
    have hlog : Nat.clog 2 X.card ≤ Nat.clog 2 n :=
      Nat.clog_mono_right 2 (ExceptionLoopMean.far_card_le R b)
    have hselectorBudget : cap * s * t * Nat.clog 2 X.card ≤ N := by
      calc
        _ = cap * (s * t * Nat.clog 2 X.card) := by ring
        _ ≤ cap * (s * t * Nat.clog 2 n) := by gcongr
        _ ≤ N := hbudget
    have hretryBudget : cap * ClassRepresentativeTrace.bitBudget
        (fun _ => X.card) t 0 s ≤ N := by
      rw [LocalFlatLaw.local_bitBudget]
      simpa [Nat.mul_assoc] using hselectorBudget
    let base : FlatTraceLaw.FlatTape N := fun _ => false
    have hhalfP : 2 * (LocalFlatLaw.localBadOutputs X.card s (P base).domain
        (numericNeighborhood G) groupedB Wbase b).card ≤ X.card ^ s := by
      rw [LocalFlatLaw.card_localBadOutputs_eq_failureSet X.card s
        (P base).domain X (P base).henum
        (numericNeighborhood G) groupedB Wbase b]
      simpa [X, b] using hhalf hfar
    let bad := LocalFlatLaw.localBadOutputs X.card s (P base).domain
      (numericNeighborhood G) groupedB Wbase b
    have hbadP (ρ : FlatTraceLaw.FlatTape N) :
        LocalFlatLaw.localBadOutputs X.card s (P ρ).domain
          (numericNeighborhood G) groupedB Wbase b = bad := by
      exact LocalSelectorAbort.localBadOutputs_congr_domain
        X.card s (P ρ).domain (P base).domain (numericNeighborhood G)
        groupedB Wbase b (hdomain ρ)
    have hvalid : bad ⊆ FlatTraceLaw.outputVectors (fun _ => X.card)
        (fun _ => 0) 0 s := by
      intro output ho
      exact (Finset.mem_filter.mp ho).1
    constructor
    · apply LocalSelectorAbort.selector_failure_count_le X.card t s cap N bad
        (P base).hpositive hselectorBudget
        (fun ρ => (F ρ).step.next.σ.vars "repairRetryStatus" = 2)
      intro ρ hs
      have hf : (F ρ).step.next.σ.vars "repairRetryStatus" = 2 ∨
          (F ρ).step.next.σ.vars "repairRetryStatus" = 3 := Or.inl hs
      obtain ⟨Q, rQ, hQbits, _hQrest, hsel, _hex⟩ := (F ρ).failure hf
      have hdomainQ (j : ℕ) (hj : j < X.card) :
          Q.domain j = (P ρ).domain j := by
        have hh := ExceptionRepairMean.prepared_same_reinputs R
          (FlatTraceLaw.flatBits ρ) (FlatTraceLaw.flatBits ρ)
          (P ρ) Q (hbits ρ) (hrest ρ) (hprep ρ) rQ
        exact (hh.2 j (hj.trans_le hXn)).symm
      have hbad := LocalSelectorAbort.localBadOutputs_congr_domain
        X.card s Q.domain (P ρ).domain (numericNeighborhood G)
        groupedB Wbase b hdomainQ
      refine ⟨(F ρ).step.attempts, (F ρ).step.attempts_le, ?_⟩
      have htrace := hsel hs
      simp only [hQbits, LoopInput.reinput] at htrace
      change LocalRepairRetriesSource.FlatSelectorFailed X.card Q.hpositive
        t s (LocalFlatLaw.localBadOutputs X.card s Q.domain
          (numericNeighborhood G) groupedB Wbase b)
        (F ρ).step.attempts (FlatTraceLaw.flatBits ρ) at htrace
      rw [hbad, hbadP ρ] at htrace
      exact htrace
    · apply ExceptionRepairMean.actual_exhaustion_count_le
        X.card t s cap N bad hvalid
        (by simpa only [bad, LocalFlatLaw.local_outputCount] using hhalfP)
        hretryBudget
        (fun ρ => (F ρ).step.next.σ.vars "repairRetryStatus" = 3)
      intro ρ hs
      have hf : (F ρ).step.next.σ.vars "repairRetryStatus" = 2 ∨
          (F ρ).step.next.σ.vars "repairRetryStatus" = 3 := Or.inr hs
      obtain ⟨Q, rQ, hQbits, _hQrest, _hsel, hex⟩ := (F ρ).failure hf
      have hdomainQ (j : ℕ) (hj : j < X.card) :
          Q.domain j = (P ρ).domain j := by
        have hh := ExceptionRepairMean.prepared_same_reinputs R
          (FlatTraceLaw.flatBits ρ) (FlatTraceLaw.flatBits ρ)
          (P ρ) Q (hbits ρ) (hrest ρ) (hprep ρ) rQ
        exact (hh.2 j (hj.trans_le hXn)).symm
      have hbad := LocalSelectorAbort.localBadOutputs_congr_domain
        X.card s Q.domain (P ρ).domain (numericNeighborhood G)
        groupedB Wbase b hdomainQ
      have htrace := hex hs
      simp only [hQbits, LoopInput.reinput] at htrace
      change LocalFlatLaw.FlatRejectedTrials X.card t s
        (LocalFlatLaw.localBadOutputs X.card s Q.domain
          (numericNeighborhood G) groupedB Wbase b)
        cap (FlatTraceLaw.flatBits ρ) at htrace
      rw [hbad, hbadP ρ] at htrace
      exact htrace
  · have hnot (ρ : FlatTraceLaw.FlatTape N) :
        (F ρ).step.next.σ.vars "repairRetryStatus" ≠ 2 ∧
        (F ρ).step.next.σ.vars "repairRetryStatus" ≠ 3 := by
      constructor <;> intro hs <;>
        have hf := (F ρ).failedFar (by simp [hs]) <;>
        exact hfar (by simpa [X, b, LoopInput.reinput] using hf)
    simp [hnot]

private def failureExponent (t cap status : ℕ) : ℕ :=
  if status = 2 then t else cap

private def failureWeight (t cap status : ℕ) : ℕ :=
  2 ^ failureExponent t cap status

private def failureCoeff (cap s status : ℕ) : ℕ :=
  if status = 2 then cap * s else 1

/-- Conditional count for the final failure on one fixed chronological
exception call. The pre-call state is selected by its actual shared prefix. -/
lemma stage_failure_count
    {B n s t bufferCap targetCap q cap k e N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (hbudget : e * (cap * (s * t * Nat.clog 2 n)) ≤ N)
    (hhalf : ∀ b ∈ E, (2 * k) / 3 <
      (ExceptionRepairMean.farDomain G A R.rep b).card →
      2 * (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b
        (ExceptionRepairMean.farDomain G A R.rep b) s).card ≤
        (ExceptionRepairMean.farDomain G A R.rep b).card ^ s)
    (final : FlatTraceLaw.FlatTape N → Env)
    (steps : FlatTraceLaw.FlatTape N → List ExecutedException)
    (hchain : ∀ ρ, StepChain
      (R.reinput (FlatTraceLaw.flatBits ρ)) (final ρ) (steps ρ))
    (hlength : ∀ ρ, (steps ρ).length ≤ e)
    (hvalid : ∀ ρ, ∀ z ∈ steps ρ,
      z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t))
    (j status : ℕ) (hj : j < e) (hz : status = 2 ∨ status = 3) :
    failureWeight t cap status *
      (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
        (final ρ).vars "repairRetryStatus" = status ∧
          (steps ρ).length = j + 1).card ≤
        failureCoeff cap s status * 2 ^ N := by
  classical
  let C := cap * (s * t * Nat.clog 2 n)
  let used (ρ : FlatTraceLaw.FlatTape N) :=
    traceBitCost G A R.rep ((steps ρ).take j)
  have hfull (ρ : FlatTraceLaw.FlatTape N) :
      traceBitCost G A R.rep (steps ρ) ≤ N := by
    have hh := traceBitCost_take_le R (steps ρ) (hvalid ρ)
      (steps ρ).length (le_refl _)
    simpa only [List.take_of_length_le (le_refl (steps ρ).length)]
      using hh.trans (by
        calc
          _ ≤ e * C := Nat.mul_le_mul_right C (hlength ρ)
          _ ≤ N := hbudget)
  have hu (ρ : FlatTraceLaw.FlatTape N) : used ρ ≤ N := by
    have hprefix : traceBitCost G A R.rep ((steps ρ).take j) ≤
        traceBitCost G A R.rep (steps ρ) := by
      conv_rhs => rw [← List.take_append_drop j (steps ρ)]
      exact traceBitCost_append_le G A R.rep _ _
    exact hprefix.trans (hfull ρ)
  have hc (ρ τ : FlatTraceLaw.FlatTape N)
      (hp : (FlatTraceLaw.flatBits ρ).take (used ρ) =
        (FlatTraceLaw.flatBits τ).take (used ρ)) : used τ = used ρ :=
    StepChain.stage_cost_causal R steps final hchain hfull j ρ τ hp
  apply count_le_of_stopped_fibers (t := failureExponent t cap status)
    (c := failureCoeff cap s status) used hu hc
    (fun ρ => (final ρ).vars "repairRetryStatus" = status ∧
      (steps ρ).length = j + 1)
  intro ρ
  let f (η : FlatTraceLaw.FlatTape (N - used ρ)) :=
    (Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
      (hu ρ)).symm
      ((Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
        (hu ρ) ρ).1, η)
  have hpre (η : FlatTraceLaw.FlatTape (N - used ρ)) :
      (FlatTraceLaw.flatBits ρ).take (used ρ) =
      (FlatTraceLaw.flatBits (f η)).take (used ρ) := by
    change (List.ofFn ρ).take (used ρ) =
      (List.ofFn (f η)).take (used ρ)
    rw [StoppedPrefixAveraging.prefix_of_split (hu ρ),
      StoppedPrefixAveraging.prefix_of_split (hu ρ)]
    simp [f]
  have hdrop (η : FlatTraceLaw.FlatTape (N - used ρ)) :
      (FlatTraceLaw.flatBits (f η)).drop (used ρ) =
        FlatTraceLaw.flatBits η := by
    have hsplit := StoppedPrefixAveraging.boolTape_split (hu ρ) (f η)
    have hpair :
        Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
          (hu ρ) (f η) =
          ((Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting.splitEquiv
            (hu ρ) ρ).1, η) := Equiv.apply_symm_apply _ _
    change (List.ofFn (f η)).drop (used ρ) = List.ofFn η
    rw [hsplit, hpair]
    simp
  by_cases hjreach : j < (steps ρ).length
  · have hprefixC : used ρ ≤ j * C := by
      simpa [used, C] using traceBitCost_take_le R (steps ρ)
        (hvalid ρ) j (by omega)
    have htailBudget : C ≤ N - used ρ := by
      have hsum : used ρ + C ≤ N := by
        calc
          _ ≤ j * C + C := Nat.add_le_add_right hprefixC C
          _ = (j + 1) * C := by ring
          _ ≤ e * C := Nat.mul_le_mul_right C (by omega)
          _ ≤ N := hbudget
      omega
    obtain ⟨Wcur, Pcur, hpref, hsuffix, hrep, hlist, hrest,
      hbits⟩ := StepChain.stage_split (hchain ρ) j (by omega)
    have hrestCur : Pcur.rest = R.rest := by
      simpa [LoopInput.reinput] using hrest
    have hbitsCur : Pcur.bits =
        (FlatTraceLaw.flatBits ρ).drop (used ρ) := by
      simpa [LoopInput.reinput, used] using hbits
    have hne : (steps ρ).drop j ≠ [] := by
      intro hn
      have hh := congrArg List.length hn
      simp only [List.length_drop, List.length_nil] at hh
      omega
    obtain ⟨i, hindex, hstop, hi⟩ := StepChain.head_ready hsuffix hne
    have hrepCur : Pcur.rep = R.rep := by
      simpa [LoopInput.reinput] using hrep
    have hbE : Pcur.exceptionList i ∈ E := by
      apply (Pcur.hprefix.2 (Pcur.exceptionList i)).mp
      have hil : i < (Stack.toList e Pcur.exceptionList).length := by
        simpa [Stack.toList] using hi
      have hget : (Stack.toList e Pcur.exceptionList)[i] =
          Pcur.exceptionList i := by simp [Stack.toList, hi]
      rw [← hget]
      exact List.getElem_mem hil
    have hhalfCur : (2 * k) / 3 <
        (ExceptionRepairMean.farDomain G A Pcur.rep
          (Pcur.exceptionList i)).card →
        2 * (SamplerLocalSuccess.localTrialFailureSet
          (numericNeighborhood G) groupedB Wbase (Pcur.exceptionList i)
          (ExceptionRepairMean.farDomain G A Pcur.rep
            (Pcur.exceptionList i)) s).card ≤
          (ExceptionRepairMean.farDomain G A Pcur.rep
            (Pcur.exceptionList i)).card ^ s := by
      intro hf
      rw [hrepCur] at hf ⊢
      exact hhalf (Pcur.exceptionList i) hbE hf
    have hcall : cap * (s * t * Nat.clog 2
        (ExceptionRepairMean.farDomain G A Pcur.rep
          (Pcur.exceptionList i)).card) ≤ N - used ρ := by
      have hlog := Nat.clog_mono_right 2
        (ExceptionLoopMean.far_card_le Pcur (Pcur.exceptionList i))
      calc
        _ ≤ C := by dsimp [C]; gcongr
        _ ≤ N - used ρ := htailBudget
    let F : ∀ η : FlatTraceLaw.FlatTape (N - used ρ),
        FailureStepRecord (Pcur.reinput (FlatTraceLaw.flatBits η)) i :=
      fun η => Classical.choice (failureStepRecord_exists
        (Pcur.reinput (FlatTraceLaw.flatBits η)) i
        (by simpa [LoopInput.reinput_state] using hindex)
        (by simpa [LoopInput.reinput_state] using hstop) hi
        (by simpa [LoopInput.reinput, ExceptionRepairMean.farDomain]
          using hcall))
    have hone := one_step_failure_counts Pcur i hindex hstop hi
      htailBudget hhalfCur F
    have honeStatus : failureWeight t cap status *
        (Finset.univ.filter fun η : FlatTraceLaw.FlatTape (N - used ρ) =>
          (F η).step.next.σ.vars "repairRetryStatus" = status).card ≤
          failureCoeff cap s status * 2 ^ (N - used ρ) := by
      rcases hz with htwo | hthree
      · subst status
        simpa [failureWeight, failureExponent, failureCoeff] using hone.1
      · subst status
        simpa [failureWeight, failureExponent, failureCoeff] using hone.2
    let bad := (Finset.univ : Finset (FlatTraceLaw.FlatTape (N - used ρ))).filter
      (fun η => (final (f η)).vars "repairRetryStatus" = status ∧
        (steps (f η)).length = j + 1)
    let first := (Finset.univ : Finset (FlatTraceLaw.FlatTape (N - used ρ))).filter
      (fun η => (F η).step.next.σ.vars "repairRetryStatus" = status)
    have hsub : bad ⊆ first := by
      intro η hη
      have hevent : (final (f η)).vars "repairRetryStatus" = status ∧
          (steps (f η)).length = j + 1 :=
        (Finset.mem_filter.mp hη).2
      let τ := f η
      obtain ⟨Wτ, Wnextτ, Qcur, Qnext, iτ, zτ, hprefτ, hdropτ,
        hrestτ, hbitsτ, hbodyτ, _hvertexτ, _hfarτ, _hfailureτ,
        hfinalτ⟩ := StepChain.failed_at_stage (hchain τ) j status
          hevent.2 hevent.1 hz
      have hrestQ : Qcur.rest = R.rest := by
        simpa [LoopInput.reinput] using hrestτ
      have hbitsQ : Qcur.bits =
          (FlatTraceLaw.flatBits τ).drop
            (traceBitCost G A R.rep ((steps τ).take j)) := by
        simpa [LoopInput.reinput] using hbitsτ
      have hlenρ : ((steps ρ).take j).length = j := by
        simp [List.length_take, Nat.min_eq_left (by omega : j ≤ (steps ρ).length)]
      have hlenτ : ((steps τ).take j).length = j := by
        have hlenτ' : (steps τ).length = j + 1 := hevent.2
        simp [List.length_take, Nat.min_eq_left (by omega : j ≤ (steps τ).length)]
      have hstate := StepChain.prefix_replay (j := j) R
        (FlatTraceLaw.flatBits ρ) (FlatTraceLaw.flatBits τ)
        Pcur Qcur ((steps ρ).take j) ((steps τ).take j)
        hpref hprefτ hlenρ hlenτ hrestCur hrestQ
        hbitsCur hbitsQ
        (by simpa [FlatTraceLaw.flatBits_length] using hu ρ)
        (by simpa [FlatTraceLaw.flatBits_length] using hu τ)
        (hpre η)
      have hstartEq : Qcur.σ =
          (Pcur.reinput (FlatTraceLaw.flatBits η)).σ := by
        simpa [LoopInput.reinput_state, hrestCur, hdrop η, τ, used]
          using hstate.2
      obtain ⟨K, rbodyτ⟩ := hbodyτ
      have rbodyτ' : Run B exceptionRepairBody
          (Pcur.reinput (FlatTraceLaw.flatBits η)).σ Qnext.σ K := by
        simpa only [← hstartEq] using rbodyτ
      obtain ⟨_, _, bigτ⟩ := rbodyτ'
      obtain ⟨_, _, bigF⟩ := (F η).step.run
      have hnextEq : Qnext.σ = (F η).step.next.σ :=
        (BigStep.unique bigτ.bigStep bigF.bigStep).1
      have hstatusF : (F η).step.next.σ.vars "repairRetryStatus" = status := by
        rw [← hnextEq, hfinalτ]
        exact hevent.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstatusF⟩
    have hcount := Nat.mul_le_mul_left (failureWeight t cap status)
      (Finset.card_le_card hsub)
    change failureWeight t cap status * bad.card ≤
      failureCoeff cap s status * 2 ^ (N - used ρ)
    exact hcount.trans (by simpa [first] using honeStatus)
  · have hjpast : (steps ρ).length ≤ j := by omega
    have hnone (η : FlatTraceLaw.FlatTape (N - used ρ)) :
        ¬ ((final (f η)).vars "repairRetryStatus" = status ∧
          (steps (f η)).length = j + 1) := by
      intro he
      have hprefixFull : (FlatTraceLaw.flatBits ρ).take
          (traceBitCost G A R.rep (steps ρ)) =
          (FlatTraceLaw.flatBits (f η)).take
            (traceBitCost G A R.rep (steps ρ)) := by
        simpa [used, List.take_of_length_le hjpast] using hpre η
      have hlen := (StepChain.same_result_same_prefix R
        (FlatTraceLaw.flatBits ρ) (FlatTraceLaw.flatBits (f η))
        (hchain ρ) (hchain (f η))
        (by simpa [FlatTraceLaw.flatBits_length] using hfull ρ)
        (by simpa [FlatTraceLaw.flatBits_length] using hfull (f η))
        hprefixFull).1
      omega
    have hzero : (Finset.univ.filter fun η : FlatTraceLaw.FlatTape
        (N - used ρ) =>
          (final (f η)).vars "repairRetryStatus" = status ∧
            (steps (f η)).length = j + 1) = ∅ := by
      ext η
      simp [hnone η]
    change 2 ^ failureExponent t cap status *
      (Finset.univ.filter fun η : FlatTraceLaw.FlatTape (N - used ρ) =>
        (final (f η)).vars "repairRetryStatus" = status ∧
          (steps (f η)).length = j + 1).card ≤
        failureCoeff cap s status * 2 ^ (N - used ρ)
    rw [hzero]
    simp

/-- The actual packed repair source aborts on status two or three only at
one of its at most `e` chronological calls. Its adaptive failure mass is
bounded on the single shared flat tape, including every rejected prefix. -/
lemma packed_failure_counts
    {B n s t bufferCap targetCap q cap k e N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wstart)
    (hbudget : e * (cap * (s * t * Nat.clog 2 n)) ≤ N)
    (hhalf : ∀ b ∈ E, (2 * k) / 3 <
      (ExceptionRepairMean.farDomain G A R.rep b).card →
      2 * (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b
        (ExceptionRepairMean.farDomain G A R.rep b) s).card ≤
        (ExceptionRepairMean.farDomain G A R.rep b).card ^ s)
    (final : FlatTraceLaw.FlatTape N → Env)
    (cost : FlatTraceLaw.FlatTape N → ℕ)
    (hrun : ∀ ρ : FlatTraceLaw.FlatTape N,
      BigStepB B exceptionRepairPackedSource
        (R.reinput (FlatTraceLaw.flatBits ρ)).σ (final ρ) (cost ρ)) :
    2 ^ t * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
      (final ρ).vars "repairRetryStatus" = 2).card ≤
        e * (cap * s) * 2 ^ N ∧
    2 ^ cap * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
      (final ρ).vars "repairRetryStatus" = 3).card ≤
        e * 2 ^ N := by
  classical
  obtain ⟨I, hfixedI, hbitsI, hrestI, hindexI, hstopI, hstatusI,
    finalLoop, steps, htrace⟩ :=
    PackedRepairTrace.packed_trace_family R hbudget final cost hrun
  have hrepI : I.rep = R.rep := hfixedI.2.1
  have hhalfI : ∀ b ∈ E, (2 * k) / 3 <
      (ExceptionRepairMean.farDomain G A I.rep b).card →
      2 * (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b
        (ExceptionRepairMean.farDomain G A I.rep b) s).card ≤
        (ExceptionRepairMean.farDomain G A I.rep b).card ^ s := by
    intro b hb hf
    rw [hrepI] at hf ⊢
    exact hhalf b hb hf
  have hchain (ρ : FlatTraceLaw.FlatTape N) := (htrace ρ).1
  have hlength (ρ : FlatTraceLaw.FlatTape N) := (htrace ρ).2.1
  have hvalid (ρ : FlatTraceLaw.FlatTape N) := (htrace ρ).2.2.1
  have hpositive (ρ : FlatTraceLaw.FlatTape N)
      (hf : (finalLoop ρ).vars "repairRetryStatus" = 2 ∨
        (finalLoop ρ).vars "repairRetryStatus" = 3) :
      0 < (steps ρ).length := by
    have hstart : (I.reinput (FlatTraceLaw.flatBits ρ)).σ.vars
          "repairRetryStatus" ≠ 2 ∧
        (I.reinput (FlatTraceLaw.flatBits ρ)).σ.vars
          "repairRetryStatus" ≠ 3 := by
      simp [LoopInput.reinput_state, hstatusI]
    obtain ⟨pref, z, heq, _⟩ :=
      StepChain.failed_final_step (hchain ρ) hstart hf
    rw [heq]
    simp
  have h2 : 2 ^ t * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
      (finalLoop ρ).vars "repairRetryStatus" = 2).card ≤
      e * (cap * s) * 2 ^ N := by
    apply count_le_of_final_stage steps
      (fun ρ => (finalLoop ρ).vars "repairRetryStatus" = 2)
    · intro ρ hf
      exact ⟨hpositive ρ (Or.inl hf), hlength ρ⟩
    · intro j hj
      simpa [failureWeight, failureExponent, failureCoeff] using
        stage_failure_count I hbudget hhalfI finalLoop steps hchain
          hlength hvalid j 2 hj (Or.inl rfl)
  have h3 : 2 ^ cap * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
      (finalLoop ρ).vars "repairRetryStatus" = 3).card ≤
      e * 2 ^ N := by
    have hh : 2 ^ cap * (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
        (finalLoop ρ).vars "repairRetryStatus" = 3).card ≤
        e * 1 * 2 ^ N := count_le_of_final_stage steps
      (fun ρ => (finalLoop ρ).vars "repairRetryStatus" = 3)
      (by
        intro ρ hf
        exact ⟨hpositive ρ (Or.inr hf), hlength ρ⟩)
      (by
        intro j hj
        simpa [failureWeight, failureExponent, failureCoeff] using
          stage_failure_count I hbudget hhalfI finalLoop steps hchain
            hlength hvalid j 3 hj (Or.inr rfl))
    simpa [mul_assoc] using hh
  have hfilter (z : ℕ) :
      (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
        (final ρ).vars "repairRetryStatus" = z).card =
      (Finset.univ.filter fun ρ : FlatTraceLaw.FlatTape N =>
        (finalLoop ρ).vars "repairRetryStatus" = z).card := by
    congr 1
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (htrace ρ).2.2.2.2 ▸ Iff.rfl
  constructor
  · simpa only [hfilter 2] using h2
  · simpa only [hfilter 3] using h3

end Lax457868Proofs.ExceptionAbortProbability
