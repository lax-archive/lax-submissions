import Lax457868Proofs.RefinedTapeReserve
import Lax457868Proofs.StoppedPrefixAveraging

/-! The exact bit count of the actual phase-three source loop is a stopping
time. This lets conditional estimates for later exception calls be averaged
over the unread suffix of each earlier run. -/

namespace Lax457868Proofs.ExceptionRepairMean

open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.LocalRepairRetriesSource
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open scoped symmDiff

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
