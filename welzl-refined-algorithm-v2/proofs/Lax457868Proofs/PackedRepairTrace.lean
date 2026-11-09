import Lax457868Proofs.ExceptionLoopMean
import Lax457868Proofs.SamplePacking

/-! The actual packed source run has a chronological trace from one fixed
initialized state on every refill of the random tape. -/
namespace Lax457868Proofs.PackedRepairTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.ExceptionRepairMean
open Lax457868Proofs.ExceptionLoopMean
open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.StoppedPrefixAveraging
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open scoped BigOperators symmDiff

private lemma traceBitCost_le_length
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (I : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (steps : List ExecutedException)
    (hvalid : ∀ z ∈ steps, z.attempts ≤ cap ∧
      z.used ≤ z.attempts*(s*t)) :
    traceBitCost G A I.rep steps ≤
      steps.length * (cap*(s*t*Nat.clog 2 n)) := by
  let C := cap*(s*t*Nat.clog 2 n)
  have hstep (z : ExecutedException) (hz : z ∈ steps) :
      ExecutedException.bitCost G A I.rep z ≤ C := by
    have hv := hvalid z hz
    have hu : z.used ≤ cap*(s*t) :=
      hv.2.trans (Nat.mul_le_mul_right (s*t) hv.1)
    have hlog : Nat.clog 2 (farDomain G A I.rep z.vertex).card ≤
        Nat.clog 2 n := Nat.clog_mono_right 2 (far_card_le I z.vertex)
    dsimp [ExecutedException.bitCost, C]
    change z.used * Nat.clog 2 (farDomain G A I.rep z.vertex).card ≤
      cap*(s*t*Nat.clog 2 n)
    calc
      _ ≤ (cap*(s*t))*Nat.clog 2 n := by gcongr
      _ = _ := by ring
  change (steps.map (ExecutedException.bitCost G A I.rep)).sum ≤
    steps.length*C
  induction steps with
  | nil => simp
  | cons z zs ih =>
      have hz : ExecutedException.bitCost G A I.rep z ≤ C :=
        hstep z (by simp)
      have htailValid : ∀ y ∈ zs, y.attempts ≤ cap ∧
          y.used ≤ y.attempts*(s*t) := by
        intro y hy
        exact hvalid y (by simp [hy])
      have htailStep : ∀ y ∈ zs,
          ExecutedException.bitCost G A I.rep y ≤ C := by
        intro y hy
        exact hstep y (by simp [hy])
      have hih := ih htailValid htailStep
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ C + zs.length*C := Nat.add_le_add hz hih
        _ = (zs.length+1)*C := by ring

/-- One initialized loop state is shared by all flat-tape executions. Each
actual packed run has the source loop chain from that state's refill, and its
visible retry status agrees with the chain's final loop state. -/
lemma packed_trace_family
    {B n s t bufferCap targetCap q cap k e N : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (hbudget : e*(cap*(s*t*Nat.clog 2 n)) ≤ N)
    (final : FlatTape N → Env) (cost : FlatTape N → ℕ)
    (hrun : ∀ ρ : FlatTape N,
      BigStepB B exceptionRepairPackedSource
        (R.reinput (flatBits ρ)).σ (final ρ) (cost ρ)) :
    ∃ I : LoopInput B n s t bufferCap targetCap q cap k e
        G x E groupedB Wbase A Wcurrent,
      SameFixed R I ∧ I.bits = R.bits ∧ I.rest = R.rest ∧
      I.σ.vars "exceptionIndex" = 0 ∧
      I.σ.vars "exceptionStop" = e ∧
      I.σ.vars "repairRetryStatus" = 1 ∧
      ∃ (finalLoop : FlatTape N → Env)
        (steps : FlatTape N → List ExecutedException),
        ∀ ρ,
          StepChain (I.reinput (flatBits ρ)) (finalLoop ρ) (steps ρ) ∧
          (steps ρ).length ≤ e ∧
          (∀ z ∈ steps ρ, z.attempts ≤ cap ∧ z.used ≤ z.attempts*(s*t)) ∧
          traceBitCost G A I.rep (steps ρ) ≤ N ∧
          (final ρ).vars "repairRetryStatus" =
            (finalLoop ρ).vars "repairRetryStatus" := by
  classical
  obtain ⟨I, rinit, hbitsI, hfixedI, hindexI, hstopI, hstatusI⟩ :=
    initialize_loop R
  have hrestI : I.rest = R.rest := hfixedI.2.2.2.2.2.1
  have hin : R.σ.inp = [] ++ I.σ.inp := by
    simp only [List.nil_append, R.hinput, I.hinput, hbitsI, hrestI]
  have hinitρ (ρ : FlatTape N) :
      Run B exceptionRepairInit (R.reinput (flatBits ρ)).σ
        (I.reinput (flatBits ρ)).σ 6 := by
    have hh := run_replace_consumed_suffix rinit [] hin
      ((flatBits ρ).map Bool.toNat ++ R.rest)
    simpa [LoopInput.reinput_state, hrestI] using hh
  have hconstructed (ρ : FlatTape N) :
      ∃ (σloop : Env) (steps : List ExecutedException),
        StepChain (I.reinput (flatBits ρ)) σloop steps ∧
        steps.length ≤ e ∧
        (∀ z ∈ steps, z.attempts ≤ cap ∧ z.used ≤ z.attempts*(s*t)) ∧
        traceBitCost G A I.rep steps ≤ N ∧
        (final ρ).vars "repairRetryStatus" = σloop.vars "repairRetryStatus" := by
    let Iρ := I.reinput (flatBits ρ)
    have hbρ : e*(cap*(s*t*Nat.clog 2 n)) ≤ Iρ.bits.length := by
      simpa [Iρ, LoopInput.reinput, flatBits_length] using hbudget
    obtain ⟨Wfin, Rfin, steps, rwhile, _hbits, _hfixed,
      _hmap, hvalid, hout, hchain⟩ :=
      loop_run_aux e Iρ 0 (by simp)
        (by simpa [Iρ, LoopInput.reinput_state] using hindexI)
        (by simpa [Iρ, LoopInput.reinput_state] using hstopI)
        (by simpa [Iρ, LoopInput.reinput_state] using hstatusI) hbρ
    have hlen : steps.length ≤ e := by
      rcases hout with hs | hf
      · omega
      · exact hf.2.2.2
    have hbit : traceBitCost G A I.rep steps ≤ N := by
      have hle := traceBitCost_le_length I steps hvalid
      have hmul := Nat.mul_le_mul_right (cap*(s*t*Nat.clog 2 n)) hlen
      exact hle.trans (hmul.trans hbudget)
    have rsource : Run B exceptionRepairLoopSource
        (R.reinput (flatBits ρ)).σ Rfin.σ
        (6 + (4 + traceRunCost x G A Iρ.rep Iρ.size Iρ.label Iρ.ord s k steps)) := by
      simpa [exceptionRepairLoopSource, Iρ] using (hinitρ ρ).seq rwhile
    have honeB : 1 < B := by have := R.hthreeB; omega
    have htail : ∃ (σout : Env) (K : ℕ),
        Run B (.ite (.eq (.var "repairRetryStatus") (.lit 1))
          packMarkedSamples .skip) Rfin.σ σout K ∧
        σout.vars "repairRetryStatus" = Rfin.σ.vars "repairRetryStatus" := by
      rcases hout with hs | hf
      · have hstatus := hs.1
        have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
            B Rfin.σ = some true := by
          simpa [hstatus] using evalB_condEq
            (evalB_var (by rw [hstatus]; exact honeB :
              Rfin.σ.vars "repairRetryStatus" < B))
            (evalB_lit honeB)
        have hflags01 : ∀ v < n, setFlag Wfin v ≤ 1 := by
          intro v _
          by_cases hv : v ∈ Wfin <;> simp [setFlag, hv]
        have hnB : n < B := by have := R.hn1B; omega
        obtain ⟨σpack, packed, rpack, _⟩ :=
          packMarkedSamples_run Rfin.hn Rfin.hsample Rfin.hord
            hflags01 hnB honeB
        have hstatusPack : σpack.vars "repairRetryStatus" =
            Rfin.σ.vars "repairRetryStatus" :=
          rpack.frame_var "repairRetryStatus" (by decide)
        have rt : Run B
            (.ite (.eq (.var "repairRetryStatus") (.lit 1))
              packMarkedSamples .skip) Rfin.σ σpack (20*n+13) := by
          have h := Run.ite_true (d := .skip) hguard rpack
          simpa [show 4+(20*n+9)=20*n+13 by omega] using h
        exact ⟨σpack, 20*n+13, rt, hstatusPack⟩
      · have hstatus : Rfin.σ.vars "repairRetryStatus" ≠ 1 := by
          rcases hf.1 with htwo | hthree <;> omega
        have hstatusB : Rfin.σ.vars "repairRetryStatus" < B := by
          rcases hf.1 with htwo | hthree <;> have := R.hthreeB <;> omega
        have hguard : (Cond.eq (.var "repairRetryStatus") (.lit 1)).evalB
            B Rfin.σ = some false := by
          simpa [hstatus] using evalB_condEq
            (evalB_var hstatusB) (evalB_lit honeB)
        have rt : Run B
            (.ite (.eq (.var "repairRetryStatus") (.lit 1))
              packMarkedSamples .skip) Rfin.σ Rfin.σ 5 := by
          simpa [Cond.size, Expr.size] using
            (Run.ite_false (c := packMarkedSamples) hguard Run.skip)
        exact ⟨Rfin.σ, 5, rt, rfl⟩
    obtain ⟨σout, K, rtail, hstatusOut⟩ := htail
    have rpacked : Run B exceptionRepairPackedSource
        (R.reinput (flatBits ρ)).σ σout
        (6 + (4 + traceRunCost x G A Iρ.rep Iρ.size Iρ.label Iρ.ord s k steps) + K) := by
      simpa [exceptionRepairPackedSource] using rsource.seq rtail
    obtain ⟨_, _, hbig⟩ := rpacked
    have hfinal : final ρ = σout :=
      (BigStep.unique (hrun ρ).bigStep hbig.bigStep).1
    exact ⟨Rfin.σ, steps, hchain, hlen, hvalid, hbit,
      by rw [hfinal]; exact hstatusOut⟩
  choose finalLoop steps hchain hlen hvalid hbit hstatus using hconstructed
  exact ⟨I, hfixedI, hbitsI, hrestI, hindexI, hstopI, hstatusI,
    finalLoop, steps, fun ρ => ⟨hchain ρ, hlen ρ, hvalid ρ,
      hbit ρ, hstatus ρ⟩⟩

end Lax457868Proofs.PackedRepairTrace
