import Lax457868Proofs.RefinedTapeReserve
import Lax457868Proofs.StoppedPrefixAveraging

/-! The exact bit count of the actual phase-three source loop is a stopping
time. This lets conditional estimates for later exception calls be averaged
over the unread suffix of each earlier run. -/

namespace Lax457868Proofs.ExceptionRepairMean

open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.LocalRepairRetriesSource
open Lax457868Proofs.LocalRepairSource
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open scoped symmDiff

/-- The fixed symmetric-difference domain of one packed exception. -/
private noncomputable def farDomain {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset ℕ) (rep : ℕ → ℕ) (b : ℕ) : Finset ℕ :=
  (numericNeighborhood G b ∩ A) ∆
    (numericNeighborhood G (rep b) ∩ A)

/-- Hide the dependent choice of the actual domain-preparation result from
later finite-sum elaboration. Its source certificate is projected below. -/
private noncomputable def chosenFarPrepared
    {B n s t bufferCap targetCap q cap k e i a u : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (bits : List Bool)
    (hfar : FarStepTrace (R.reinput bits) i a u) :
    ReadyInput B n (farDomain G A R.rep (R.exceptionList i)).card n
      s t bufferCap targetCap q (R.exceptionList i) G x
      (farDomain G A R.rep (R.exceptionList i)) groupedB Wbase Wcurrent :=
  Classical.choose hfar

private lemma chosenFarPrepared_spec
    {B n s t bufferCap targetCap q cap k e i a u : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (bits : List Bool)
    (hfar : FarStepTrace (R.reinput bits) i a u) :
    let P := chosenFarPrepared R bits hfar
    let b := R.exceptionList i
    let X := farDomain G A R.rep b
    Run B ((Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
      RepairFilterSource.repairDomainSource)
      (R.reinput bits).σ P.σ (3 + domainCharge x G A R.rep b) ∧
    P.bits = bits ∧ P.rest = R.rest ∧
    P.scanUpper = classScanCharge x R.size R.label R.ord b ∧
    ∃ σsource : Env,
      Run B localRepairRetriesSource P.σ σsource
        (12 * Nat.clog 2 X.card + 24 +
          ((15 * Nat.clog 2 X.card + 30) * u +
            a * (79 * s + P.scanUpper + 50) + 14)) ∧
      σsource.vars "repairRetriesLeft" + a = cap ∧
      σsource.inp =
        (P.bits.drop (u * Nat.clog 2 X.card)).map Bool.toNat ++ P.rest := by
  unfold chosenFarPrepared
  obtain ⟨hr, hb, hrest, hscan, σsource, hrun,
    _hreject, _hfull, hcount, hinp, _hexhaust, _hselector⟩ :=
    Classical.choose_spec hfar
  exact ⟨hr, hb, hrest, hscan, σsource, hrun, hcount, hinp⟩

attribute [irreducible] chosenFarPrepared

/-- Two actual executions of the same local retry source agree on their
trial count. At positive selector width the exact unread suffix also fixes the
number of inspected blocks. -/
lemma retry_parameters_same
    {B n m domainCap s t bufferCap targetCap q b cap a u a' u' K K' : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (P : ReadyInput B n m domainCap s t bufferCap targetCap q b
      G x X groupedB Wbase Wcurrent)
    {σ τ : Env}
    (hrun : Run B localRepairRetriesSource P.σ σ K)
    (hrun' : Run B localRepairRetriesSource P.σ τ K')
    (hcount : σ.vars "repairRetriesLeft" + a = cap)
    (hcount' : τ.vars "repairRetriesLeft" + a' = cap)
    (hinp : σ.inp =
      (P.bits.drop (u * Nat.clog 2 m)).map Bool.toNat ++ P.rest)
    (hinp' : τ.inp =
      (P.bits.drop (u' * Nat.clog 2 m)).map Bool.toNat ++ P.rest)
    (hu : u * Nat.clog 2 m ≤ P.bits.length)
    (hu' : u' * Nat.clog 2 m ≤ P.bits.length) :
    a = a' ∧ (0 < Nat.clog 2 m → u = u') := by
  obtain ⟨_, _, hbig⟩ := hrun
  obtain ⟨_, _, hbig'⟩ := hrun'
  have heq : σ = τ := (BigStep.unique hbig.bigStep hbig'.bigStep).1
  constructor
  · rw [heq] at hcount
    omega
  · intro hL
    have hlength : P.bits.length - u * Nat.clog 2 m =
        P.bits.length - u' * Nat.clog 2 m := by
      have hinpEq : σ.inp = τ.inp := congrArg Env.inp heq
      have h := congrArg List.length (hinp.symm.trans (hinpEq.trans hinp'))
      simp only [List.length_append, List.length_map,
        List.length_drop] at h
      omega
    have hmul : u * Nat.clog 2 m = u' * Nat.clog 2 m := by omega
    exact Nat.eq_of_mul_eq_mul_right hL hmul

/-- A conditional mean bound for the actual local retry executions. The
recorded attempts and inspected blocks are identified with the canonical
stopped-trace family by source determinism and the final unread suffix. -/
lemma local_actual_mean_runtime
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
    (hL : 0 < Nat.clog 2 m)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s)
    (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) → ℕ)
    (finalState : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) → Env)
    (hactual : ∀ tape,
      Run B localRepairRetriesSource (R tape).σ (finalState tape)
        (12 * Nat.clog 2 m + 24 +
          ((15 * Nat.clog 2 m + 30) * used tape +
            attempts tape * (79 * s + scanUpper + 50) + 14)) ∧
      (finalState tape).vars "repairRetriesLeft" + attempts tape = cap ∧
      (finalState tape).inp =
        ((R tape).bits.drop (used tape * Nat.clog 2 m)).map Bool.toNat ++
          (R tape).rest ∧
      attempts tape ≤ cap ∧ used tape ≤ attempts tape * (s * t)) :
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
  obtain ⟨attempts', used', finalState', hmodel, hmean⟩ :=
    localRepairRetriesSource_mean_runtime_stopped_suffix_domain_prefix_trace
      domain R hbits hstate hdomain hscan hcap hcapB hblocks henum hhalf
  have husedBound (tape : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail))
      (a u : ℕ) (ha : a ≤ cap) (hu : u ≤ a * (s * t)) :
      u * Nat.clog 2 m ≤ (R tape).bits.length := by
    have hlen : (R tape).bits.length =
        Nblocks * Nat.clog 2 m + Ntail := by
      rw [hbits tape, FlatTraceLaw.flatBits_length]
    rw [hlen]
    calc
      u * Nat.clog 2 m ≤ (a * (s * t)) * Nat.clog 2 m :=
        Nat.mul_le_mul_right _ hu
      _ ≤ (cap * (s * t)) * Nat.clog 2 m :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ha)
      _ ≤ Nblocks * Nat.clog 2 m := Nat.mul_le_mul_right _ hblocks
      _ ≤ Nblocks * Nat.clog 2 m + Ntail := Nat.le_add_right _ _
  have hparameters (tape : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail)) :
      attempts tape = attempts' tape ∧ used tape = used' tape := by
    obtain ⟨hr, hc, hi, ha, hu⟩ := hactual tape
    obtain ⟨hr', hc', hi', ha', hu'⟩ := hmodel tape
    exact ⟨(retry_parameters_same (R tape) hr hr' hc hc' hi hi'
      (husedBound tape _ _ ha hu) (husedBound tape _ _ ha' hu')).1,
      (retry_parameters_same (R tape) hr hr' hc hc' hi hi'
      (husedBound tape _ _ ha hu) (husedBound tape _ _ ha' hu')).2 hL⟩
  convert hmean using 1
  apply Finset.sum_congr rfl
  intro tape _
  rw [(hparameters tape).1, (hparameters tape).2]

private def localActualCharge (L s scan a u : ℕ) : ℕ :=
  12 * L + 24 + ((15 * L + 30) * u + a * (79 * s + scan + 50) + 14)

private def localMeanBound (L s scan : ℕ) : ℕ :=
  12 * L + 38 + 4 * s * (15 * L + 30) +
    2 * (79 * s + scan + 50)

private lemma local_actual_mean_runtime_short
    {B n m domainCap s t bufferCap targetCap q b cap Nblocks Ntail scan : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (domain : ℕ → ℕ)
    (P : FlatTraceLaw.FlatTape (Nblocks * Nat.clog 2 m + Ntail) →
      ReadyInput B n m domainCap s t bufferCap targetCap q b
        G x X groupedB Wbase Wcurrent)
    (hbits : ∀ ρ, (P ρ).bits = FlatTraceLaw.flatBits ρ)
    (hstate : ∀ ρ τ,
      (P ρ).σ.vars = (P τ).σ.vars ∧
      (P ρ).σ.arrs = (P τ).σ.arrs ∧
      (P ρ).σ.out = (P τ).σ.out)
    (hdomain : ∀ ρ j, j < domainCap → (P ρ).domain j = domain j)
    (hscan : ∀ ρ, (P ρ).scanUpper = scan)
    (hcap : ∀ ρ, (P ρ).σ.vars "repairRetryCap" = cap)
    (hcapB : cap < B)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (hL : 0 < Nat.clog 2 m)
    (henum : PrefixEnumerates m domain X)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase b X s).card ≤ X.card ^ s)
    (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) → ℕ)
    (finalState : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 m + Ntail) → Env)
    (hactual : ∀ ρ,
      Run B localRepairRetriesSource (P ρ).σ (finalState ρ)
        (localActualCharge (Nat.clog 2 m) s (P ρ).scanUpper
          (attempts ρ) (used ρ)) ∧
      (finalState ρ).vars "repairRetriesLeft" + attempts ρ = cap ∧
      (finalState ρ).inp =
        ((P ρ).bits.drop (used ρ * Nat.clog 2 m)).map Bool.toNat ++
          (P ρ).rest ∧
      attempts ρ ≤ cap ∧ used ρ ≤ attempts ρ * (s * t)) :
    (∑ ρ, ((localActualCharge (Nat.clog 2 m) s scan
      (attempts ρ) (used ρ) : ℕ) : ℚ)) ≤
      (localMeanBound (Nat.clog 2 m) s scan : ℚ) *
        (2 ^ (Nblocks * Nat.clog 2 m + Ntail) : ℚ) := by
  have hmean := local_actual_mean_runtime domain P hbits hstate hdomain
    hscan hcap hcapB hblocks hL henum hhalf attempts used finalState
    (by
      intro ρ
      have ha := hactual ρ
      rw [hscan ρ] at ha
      simpa only [localActualCharge] using ha)
  simpa only [localActualCharge, localMeanBound] using hmean

set_option maxHeartbeats 2000000 in
/-- Conditional expected charge for actual far-repair source runs after
refilling the unread tape at a fixed exception state. -/
lemma far_step_mean_on_reinputs
    {B n s t bufferCap targetCap q cap k e i Nblocks Ntail : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (hblocks : cap * (s * t) ≤ Nblocks)
    (hL : 0 < Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet
        (numericNeighborhood G) groupedB Wbase (R.exceptionList i)
        (farDomain G A R.rep (R.exceptionList i)) s).card ≤
        (farDomain G A R.rep (R.exceptionList i)).card ^ s)
    (attempts used : FlatTraceLaw.FlatTape
      (Nblocks * Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card +
        Ntail) → ℕ)
    (hfar : ∀ ρ, FarStepTrace
      (R.reinput (FlatTraceLaw.flatBits ρ)) i (attempts ρ) (used ρ))
    (hvalid : ∀ ρ, attempts ρ ≤ cap ∧
      used ρ ≤ attempts ρ * (s * t)) :
    let L := Nat.clog 2 (farDomain G A R.rep (R.exceptionList i)).card
    let scan := classScanCharge x R.size R.label R.ord (R.exceptionList i)
    (∑ ρ, ((localActualCharge L s scan (attempts ρ) (used ρ) : ℕ) : ℚ)) ≤
      (localMeanBound L s scan : ℚ) *
        (2 ^ (Nblocks * L + Ntail) : ℚ) := by
  classical
  let b := R.exceptionList i
  let X := farDomain G A R.rep b
  let L := Nat.clog 2 X.card
  let N := Nblocks * L + Ntail
  let T := FlatTraceLaw.FlatTape N
  let F (ρ : T) := R.reinput (FlatTraceLaw.flatBits ρ)
  let P (ρ : T) := chosenFarPrepared R (FlatTraceLaw.flatBits ρ) (hfar ρ)
  have hP (ρ : T) := chosenFarPrepared_spec R (FlatTraceLaw.flatBits ρ)
    (hfar ρ)
  let ρzero : T := fun _ => false
  let domain := (P ρzero).domain
  have hfixed (ρ τ : T) :
      (P τ).σ = {(P ρ).σ with inp :=
        (FlatTraceLaw.flatBits τ).map Bool.toNat ++ R.rest} := by
    obtain ⟨rρ, hbρ, hrρ, _, _⟩ := hP ρ
    obtain ⟨rτ, _hbτ, _hrτ, _, _⟩ := hP τ
    have hin : (F ρ).σ.inp = [] ++ (P ρ).σ.inp := by
      simp only [List.nil_append]
      have hp := (P ρ).hinput
      rw [hbρ, hrρ] at hp
      exact (F ρ).hinput.trans hp.symm
    have hstart : (F τ).σ = {(F ρ).σ with inp :=
        ((FlatTraceLaw.flatBits τ).map Bool.toNat) ++ R.rest} := by
      simp [F, LoopInput.reinput_state]
    have rr : Run B
        ((Com.assign "repairB" (.get "exceptionList" (.var "exceptionIndex"))).seq
          RepairFilterSource.repairDomainSource)
        {(F ρ).σ with inp := [] ++
          ((FlatTraceLaw.flatBits τ).map Bool.toNat ++ R.rest)}
        (P τ).σ (3 + domainCharge x G A R.rep b) := by
      simpa only [List.nil_append, ← hstart] using rτ
    have hsame := StoppedPrefixAveraging.run_result_same_prefix
      rρ [] hin ((FlatTraceLaw.flatBits τ).map Bool.toNat ++ R.rest) rr
    simpa using hsame
  have hstate (ρ τ : T) :
      (P ρ).σ.vars = (P τ).σ.vars ∧
      (P ρ).σ.arrs = (P τ).σ.arrs ∧
      (P ρ).σ.out = (P τ).σ.out := by
    rw [hfixed ρ τ]
    simp
  have hdomain (ρ : T) (j : ℕ) (hj : j < n) :
      (P ρ).domain j = domain j := by
    have harr : arrOf n (P ρ).domain = arrOf n domain := by
      calc
        arrOf n (P ρ).domain = (P ρ).σ.arrs "drawDomain" :=
          (P ρ).hdomain.symm
        _ = (P ρzero).σ.arrs "drawDomain" := (hstate ρ ρzero).2.1 ▸ rfl
        _ = arrOf n domain := (P ρzero).hdomain
    exact InitialFlatLaw.arrOf_eq_on harr j hj
  have hbits (ρ : T) : (P ρ).bits = FlatTraceLaw.flatBits ρ :=
    (hP ρ).2.1
  have hscan (ρ : T) : (P ρ).scanUpper =
      classScanCharge x R.size R.label R.ord b :=
    (hP ρ).2.2.2.1
  have hcap (ρ : T) : (P ρ).σ.vars "repairRetryCap" = cap := by
    have hprep := (hP ρ).1
    have hh := hprep.frame_var "repairRetryCap" (by decide)
    simpa [F, LoopInput.reinput_state] using hh.trans R.hretryCap
  let finalState (ρ : T) : Env := Classical.choose ((hP ρ).2.2.2.2)
  have hactual (ρ : T) :
      Run B localRepairRetriesSource (P ρ).σ (finalState ρ)
        (localActualCharge L s (P ρ).scanUpper (attempts ρ) (used ρ)) ∧
      (finalState ρ).vars "repairRetriesLeft" + attempts ρ = cap ∧
      (finalState ρ).inp =
        ((P ρ).bits.drop (used ρ * L)).map Bool.toNat ++ (P ρ).rest ∧
      attempts ρ ≤ cap ∧ used ρ ≤ attempts ρ * (s * t) := by
    have hs := Classical.choose_spec ((hP ρ).2.2.2.2)
    exact ⟨hs.1, hs.2.1, hs.2.2, (hvalid ρ).1, (hvalid ρ).2⟩
  exact local_actual_mean_runtime_short
    (B := B) (n := n) (m := X.card) (domainCap := n)
    (s := s) (t := t) (bufferCap := bufferCap)
    (targetCap := targetCap) (q := q) (b := b) (cap := cap)
    (Nblocks := Nblocks) (Ntail := Ntail)
    (scan := classScanCharge x R.size R.label R.ord b)
    (G := G) (x := x) (X := X) (groupedB := groupedB)
    (Wbase := Wbase) (Wcurrent := Wcurrent)
    domain P hbits hstate hdomain hscan hcap R.hcapB hblocks hL
    (P ρzero).henum hhalf attempts used finalState hactual

/-- A status-three source event is contained in the exact stopped-prefix
fiber of `cap` rejected trials. Its count decays geometrically on the full
flat tape, including all unread bits. -/
lemma actual_exhaustion_count_le
    (m t s cap Nbits : ℕ) (bad : Finset (List ℕ))
    (hvalid : bad ⊆ FlatTraceLaw.outputVectors (fun _ => m)
      (fun _ => 0) 0 s)
    (hhalf : 2 * bad.card ≤ FlatTraceLaw.outputCount (fun _ => m) 0 s)
    (hbudget : cap * ClassRepresentativeTrace.bitBudget
      (fun _ => m) t 0 s ≤ Nbits)
    (exhausted : FlatTraceLaw.FlatTape Nbits → Prop)
    [DecidablePred exhausted]
    (htrace : ∀ tape, exhausted tape →
      LocalFlatLaw.FlatRejectedTrials m t s bad cap
        (FlatTraceLaw.flatBits tape)) :
    2 ^ cap * (Finset.univ.filter exhausted).card ≤ 2 ^ Nbits := by
  classical
  have hsubset : (Finset.univ.filter exhausted) ⊆
      LocalFlatLaw.retryRejectedFiber m t s cap Nbits bad := by
    intro tape htape
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      htrace tape (Finset.mem_filter.mp htape).2⟩
  calc
    2 ^ cap * (Finset.univ.filter exhausted).card ≤
        2 ^ cap *
          (LocalFlatLaw.retryRejectedFiber m t s cap Nbits bad).card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card hsubset)
    _ ≤ 2 ^ Nbits :=
      LocalFlatLaw.retryRejectedFiber_geometric m t s bad hvalid hhalf
        cap Nbits hbudget

/-- Keep the domain and repeated class-scan work explicit while replacing
each local selector width by the one global width `clog 2 n`. The bound uses
the actual successful draw count, so it has no factor of the selector cap. -/
lemma step_runCost_le
    {n s k : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A : Finset ℕ} (hA : A ⊆ Finset.range n)
    (rep size label ord : ℕ → ℕ) (z : ExecutedException) :
    z.runCost x G A rep size label ord s k ≤
      domainCharge x G A rep z.vertex + 60 + 12 * Nat.clog 2 n +
        (15 * Nat.clog 2 n + 30) * z.used +
        z.attempts *
          (79 * s + classScanCharge x size label ord z.vertex + 50) := by
  let X := (numericNeighborhood G z.vertex ∩ A) ∆
    (numericNeighborhood G (rep z.vertex) ∩ A)
  have hX : X ⊆ A := by
    intro v hv
    simp only [X, Finset.mem_symmDiff, Finset.mem_inter] at hv
    tauto
  have hcard : X.card ≤ n := by
    have hh := (Finset.card_le_card hX).trans (Finset.card_le_card hA)
    simpa using hh
  have hlog : Nat.clog 2 X.card ≤ Nat.clog 2 n :=
    Nat.clog_mono_right 2 hcard
  have hmul :
      (15 * Nat.clog 2 X.card + 30) * z.used ≤
        (15 * Nat.clog 2 n + 30) * z.used := by
    gcongr
  change 4 + (domainCharge x G A rep z.vertex +
      (if X.card ≤ (2 * k) / 3 then 6 else
        4 + (12 * Nat.clog 2 X.card + 24 +
          ((15 * Nat.clog 2 X.card + 30) * z.used +
            z.attempts *
              (79 * s + classScanCharge x size label ord z.vertex + 50) + 14)))) +
      (if z.completed then 11 else 9) ≤ _
  split_ifs <;> omega

/-- Sum the actual ordered exception charges, retaining the potentially
repeated representative-domain and class-scan terms for later averaging. -/
lemma traceRunCost_le
    {n s k : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A : Finset ℕ} (hA : A ⊆ Finset.range n)
    (rep size label ord : ℕ → ℕ) (steps : List ExecutedException) :
    traceRunCost x G A rep size label ord s k steps ≤
      (steps.map fun z =>
        domainCharge x G A rep z.vertex + 60 + 12 * Nat.clog 2 n +
          (15 * Nat.clog 2 n + 30) * z.used +
          z.attempts *
            (79 * s + classScanCharge x size label ord z.vertex + 50)).sum := by
  induction steps with
  | nil => simp [traceRunCost]
  | cons z zs ih =>
      simp only [traceRunCost, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (step_runCost_le hA rep size label ord z) ih

/-- Replacing bits after the complete exception loop's observed prefix cannot
change its number of consumed bits. The recorded `steps` may contain stopped
failed retries; only their actual draw counts enter `traceBitCost`. -/
lemma loop_used_causal
    {B n s t bufferCap targetCap q cap k e N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : FlatTraceLaw.FlatTape N →
      LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wstart)
    (hbits : ∀ ρ, (R ρ).bits = FlatTraceLaw.flatBits ρ)
    (hstate : ∀ ρ τ,
      (R ρ).σ.vars = (R τ).σ.vars ∧
      (R ρ).σ.arrs = (R τ).σ.arrs ∧
      (R ρ).σ.out = (R τ).σ.out)
    (hbudget : e * (cap * (s * t * Nat.clog 2 n)) ≤ N)
    (final : FlatTraceLaw.FlatTape N → Env)
    (steps : FlatTraceLaw.FlatTape N → List ExecutedException)
    (hrun : ∀ ρ, Run B exceptionRepairLoopSource (R ρ).σ (final ρ)
      (10 + traceRunCost x G A (R ρ).rep (R ρ).size
        (R ρ).label (R ρ).ord s k (steps ρ)))
    (hinp : ∀ ρ, (final ρ).inp =
      ((R ρ).bits.drop (traceBitCost G A (R ρ).rep (steps ρ))).map
        Bool.toNat ++ (R ρ).rest)
    (hmap : ∀ ρ, (steps ρ).map ExecutedException.vertex =
      (Stack.toList e (R ρ).exceptionList).take (steps ρ).length)
    (hvalid : ∀ ρ z, z ∈ steps ρ →
      z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t)) :
    ∀ ρ τ,
      (FlatTraceLaw.flatBits ρ).take
          (traceBitCost G A (R ρ).rep (steps ρ)) =
        (FlatTraceLaw.flatBits τ).take
          (traceBitCost G A (R ρ).rep (steps ρ)) →
      traceBitCost G A (R τ).rep (steps τ) =
        traceBitCost G A (R ρ).rep (steps ρ) := by
  intro ρ τ hprefix
  let used (η : FlatTraceLaw.FlatTape N) :=
    traceBitCost G A (R η).rep (steps η)
  have hused (η : FlatTraceLaw.FlatTape N) : used η ≤ N := by
    have hlen := steps_length_le (hmap η)
    exact (traceBitCost_le (R η).hA hlen (hvalid η)).trans hbudget
  have hstart (η : FlatTraceLaw.FlatTape N) :
      (R η).σ.inp =
        ((FlatTraceLaw.flatBits η).map Bool.toNat) ++ (R η).rest := by
    rw [(R η).hinput, hbits η]
  have hend (η : FlatTraceLaw.FlatTape N) :
      (final η).inp =
        ((FlatTraceLaw.flatBits η).map Bool.toNat).drop (used η) ++
          (R η).rest := by
    rw [hinp η, hbits η]
    simp [used, List.map_drop]
  have hwords :
      (((FlatTraceLaw.flatBits ρ).map Bool.toNat).take (used ρ)) =
        (((FlatTraceLaw.flatBits τ).map Bool.toNat).take (used ρ)) := by
    simpa only [List.map_take] using congrArg (List.map Bool.toNat) hprefix
  obtain ⟨hv, ha, ho⟩ := hstate ρ τ
  have heq := run_consumption_causal hv ha ho
    (hstart ρ) (hstart τ) (hend ρ) (hend τ)
    (by simpa [FlatTraceLaw.flatBits_length] using hused ρ)
    (by simpa [FlatTraceLaw.flatBits_length] using hused ρ)
    (by simpa [FlatTraceLaw.flatBits_length] using hused τ)
    hwords (hrun ρ) (hrun τ)
  exact heq.symm

/-- Choose the actual source executions simultaneously over all flat tapes.
The poststate, ordered repair trace, and stopping-time bit count belong to
the same run on every tape. -/
lemma loop_runs_and_stopping_time
    {B n s t bufferCap targetCap q cap k e N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wstart : Finset ℕ}
    (R : FlatTraceLaw.FlatTape N →
      LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wstart)
    (hbits : ∀ ρ, (R ρ).bits = FlatTraceLaw.flatBits ρ)
    (hstate : ∀ ρ τ,
      (R ρ).σ.vars = (R τ).σ.vars ∧
      (R ρ).σ.arrs = (R τ).σ.arrs ∧
      (R ρ).σ.out = (R τ).σ.out)
    (hbudget : e * (cap * (s * t * Nat.clog 2 n)) ≤ N) :
    ∃ (Wfinal : FlatTraceLaw.FlatTape N → Finset ℕ)
      (Rfinal : ∀ ρ, LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A (Wfinal ρ))
      (steps : FlatTraceLaw.FlatTape N → List ExecutedException),
      (∀ ρ,
        Run B exceptionRepairLoopSource (R ρ).σ (Rfinal ρ).σ
          (10 + traceRunCost x G A (R ρ).rep (R ρ).size
            (R ρ).label (R ρ).ord s k (steps ρ)) ∧
        (Rfinal ρ).bits =
          (R ρ).bits.drop (traceBitCost G A (R ρ).rep (steps ρ)) ∧
        SameFixed (R ρ) (Rfinal ρ) ∧
        (steps ρ).map ExecutedException.vertex =
          (Stack.toList e (R ρ).exceptionList).take (steps ρ).length ∧
        (∀ z ∈ steps ρ,
          z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t))) ∧
      (∀ ρ τ,
        (FlatTraceLaw.flatBits ρ).take
            (traceBitCost G A (R ρ).rep (steps ρ)) =
          (FlatTraceLaw.flatBits τ).take
            (traceBitCost G A (R ρ).rep (steps ρ)) →
        traceBitCost G A (R τ).rep (steps τ) =
          traceBitCost G A (R ρ).rep (steps ρ)) := by
  classical
  have hex (ρ : FlatTraceLaw.FlatTape N) :
      ∃ (W : Finset ℕ)
        (P : LoopInput B n s t bufferCap targetCap q cap k e
          G x E groupedB Wbase A W)
        (zs : List ExecutedException),
        Run B exceptionRepairLoopSource (R ρ).σ P.σ
          (10 + traceRunCost x G A (R ρ).rep (R ρ).size
            (R ρ).label (R ρ).ord s k zs) ∧
        P.bits = (R ρ).bits.drop
          (traceBitCost G A (R ρ).rep zs) ∧
        SameFixed (R ρ) P ∧
        zs.map ExecutedException.vertex =
          (Stack.toList e (R ρ).exceptionList).take zs.length ∧
        (∀ z ∈ zs,
          z.attempts ≤ cap ∧ z.used ≤ z.attempts * (s * t)) := by
    have hlength : e * (cap * (s * t * Nat.clog 2 n)) ≤
        (R ρ).bits.length := by simpa [hbits ρ] using hbudget
    obtain ⟨W, P, zs, hr, hb, hf, hm, hv, _⟩ :=
      exceptionRepairLoop_run (R ρ) hlength
    exact ⟨W, P, zs, hr, hb, hf, hm, hv⟩
  choose Wfinal Rfinal steps hr hb hf hm hv using hex
  refine ⟨Wfinal, Rfinal, steps, ?_, ?_⟩
  · intro ρ
    exact ⟨hr ρ, hb ρ, hf ρ, hm ρ, hv ρ⟩
  · apply loop_used_causal R hbits hstate hbudget
      (fun ρ => (Rfinal ρ).σ) steps hr
    · intro ρ
      rw [(Rfinal ρ).hinput, hb ρ, (hf ρ).2.2.2.2.2.1]
    · exact hm
    · intro ρ z hz
      exact hv ρ z hz

end Lax457868Proofs.ExceptionRepairMean
