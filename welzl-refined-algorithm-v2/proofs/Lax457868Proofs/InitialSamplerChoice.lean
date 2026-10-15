import Lax457868Proofs.InitialSamplerAttempt
import Lax457868Proofs.SamplerPhases

/-! Proof-side bridge from the executed initial sampler to the existing
`InitialChoice` interface. -/

namespace Lax457868Proofs.InitialSamplerChoice

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.InitialDrawSampleSource
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.SequentialDraws
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Restricting each neighborhood to `A` does not change its trace on a sample
that is contained in `A`. -/
lemma restrictedNeighborhood_trace_eq
    {α β : Type*} [DecidableEq α] (N : β → Finset α)
    {A W : Finset α} (hWA : W ⊆ A) (b : β) :
    trace (fun v => N v ∩ A) W b = trace N W b := by
  ext a
  simp only [trace, Finset.mem_inter]
  constructor
  · rintro ⟨⟨haN, _haA⟩, haW⟩
    exact ⟨haN, haW⟩
  · rintro ⟨haN, haW⟩
    exact ⟨⟨haN, hWA haW⟩, haW⟩

/-- Turn concrete draw, class, and representative facts into the established
`InitialChoice` object. The map formula makes the selected representative
constant on each label class. -/
lemma initialChoice_of_actual
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β} {N : β → Finset α} {r : ℕ}
    (draws : List α) (W : Finset α) (label : β → ℕ)
    (mapped : β → β) (code : ℕ → β)
    (hdrawLength : draws.length = r)
    (hdrawMem : ∀ a ∈ draws, a ∈ A)
    (hW : W = draws.toFinset)
    (hclasses : ∀ b ∈ B, ∀ b' ∈ B,
      (label b = label b' ↔ trace N W b = trace N W b'))
    (hrepMem : ∀ b ∈ B, mapped b ∈ B)
    (hrepLabel : ∀ b ∈ B, label (mapped b) = label b)
    (hrepFormula : ∀ b ∈ B, mapped b = code (label b)) :
    ∃ choice : InitialChoice A B (fun b => N b ∩ A) r,
      choice.draws = draws ∧ choice.sample = W ∧
      ∀ b ∈ B, choice.representative b = mapped b := by
  let choice : InitialChoice A B (fun b => N b ∩ A) r := {
    draws := draws
    draws_length := hdrawLength
    draws_mem := hdrawMem
    representative := mapped
    representative_mem := hrepMem
    representative_trace := by
      intro b hb
      have hdrawSubset : draws.toFinset ⊆ A := by
        intro a ha
        exact hdrawMem a (List.mem_toFinset.mp ha)
      rw [restrictedNeighborhood_trace_eq N hdrawSubset (mapped b),
        restrictedNeighborhood_trace_eq N hdrawSubset b]
      simpa [hW] using
        ((hclasses b hb (mapped b) (hrepMem b hb)).mp
          (hrepLabel b hb).symm).symm
    representative_constant := by
      intro b hb b' hb' htrace
      have hdrawSubset : draws.toFinset ⊆ A := by
        intro a ha
        exact hdrawMem a (List.mem_toFinset.mp ha)
      have hrawDraw : trace N draws.toFinset b = trace N draws.toFinset b' := by
        rw [← restrictedNeighborhood_trace_eq N hdrawSubset b,
          ← restrictedNeighborhood_trace_eq N hdrawSubset b']
        exact htrace
      have hlabel : label b = label b' := by
        exact (hclasses b hb b' hb').mpr (by simpa [hW] using hrawDraw)
      calc
        mapped b = code (label b) := hrepFormula b hb
        _ = code (label b') := by rw [hlabel]
        _ = mapped b' := (hrepFormula b' hb').symm
  }
  refine ⟨choice, rfl, ?_, ?_⟩
  · simp [choice, InitialChoice.sample, hW]
  · intro b hb
    rfl

/-- The checked source keeps draw failure explicit. When both the draw and
representative stages succeed, it yields an `InitialChoice` whose draws and
representative map are exactly those written by the source. -/
lemma initialSamplerAttempt_run_choice
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Input B n m domainCap r t bufferCap targetCap Q G x A) :
    ∃ (σ' : Env) (tape : Fin (r * t) → Fin (Nat.clog 2 m) → Bool)
      (tail : List Bool) (values : List (Fin m)) (used : ℕ)
      (drawFailed : Bool) (stageCost : ℕ),
      I.bits = tapeBits tape ++ tail ∧
      DrawTrace m I.hmPos t r (List.ofFn tape) values used drawFailed ∧
      Run B initialSamplerAttempt I.σ σ'
        (2 + initialDrawSampleCost n m used
          (values.length + if drawFailed then 1 else 0) values.length drawFailed +
          (if drawFailed then 5 else 4 + stageCost)) ∧
      σ'.vars "batchFailed" = (if drawFailed then 1 else 0) ∧
      (drawFailed = true →
        σ'.arrs "sampleFlags" = arrOf n (fun _ => 0) ∧
        σ'.vars "sampleCount" = 0) ∧
      (drawFailed = false →
        ∃ (W : Finset ℕ) (repFailed : Bool) (draws : List ℕ),
          W = (values.map (fun i => I.domain i.val)).toFinset ∧
          W ⊆ A ∧ values.length = r ∧
          draws = values.map (fun i => I.domain i.val) ∧
          σ'.vars "repFailed" = (if repFailed then 1 else 0) ∧
          (repFailed = false →
            ∃ mapped, σ'.arrs "repB" = arrOf n mapped ∧
            ∃ choice : InitialChoice A (activeVertices n I.activeB)
                (fun b => numericNeighborhood G b ∩ A) r,
              choice.draws = draws ∧ choice.sample = W ∧
              ∀ b ∈ activeVertices n I.activeB,
                choice.representative b = mapped b)) := by
  obtain ⟨_σd, σ', tape, tail, values, used, drawFailed, stageCost,
    hbits, hdrawTrace, hrun, _haccepted, _hn, _hqpow, hbatchFailed,
    _harrFrame, _hvarFrame, hdrawFailure, hdrawSuccess⟩ :=
      initialSamplerAttempt_run_bits I
  refine ⟨σ', tape, tail, values, used, drawFailed, stageCost,
    hbits, hdrawTrace, hrun, hbatchFailed, ?_, ?_⟩
  · intro hfailed
    exact ⟨(hdrawFailure hfailed).2.1, (hdrawFailure hfailed).2.2⟩
  · intro hsuccess
    obtain ⟨W, sampleOrd, sampleCount, σp, q, label, size, xs, sorted,
      repValues, repUsed, repCharge, repFailed, hW, hWsubset, hWcard,
      hvaluesLength, _hprefix, _hpartition, _hsizes, _hoccupied, hclasses,
      _hselection, _hnFinal, _hqpowFinal, _hsampleCount, _hclassB,
      _hclassSize, _hord, _hnodup, hxs, _htrace, hrepFailedVal,
      _hrepFailure, _hsampleFlags, _hinp, hrepSuccess, _hcost⟩ :=
        hdrawSuccess hsuccess
    let draws : List ℕ := values.map (fun i => I.domain i.val)
    have hrepSuccessVal : σ'.vars "repFailed" =
        (if repFailed then 1 else 0) := hrepFailedVal
    refine ⟨W, repFailed, draws,
      hW, hWsubset, hvaluesLength, rfl, hrepSuccessVal, ?_⟩
    intro hrepOK
    obtain ⟨mapped, hmappedArr, _hvFinal, hformula, hrepClass⟩ :=
      hrepSuccess hrepOK
    refine ⟨mapped, hmappedArr, ?_⟩
    have hdrawsLength : draws.length = r := by
      simp [draws, hvaluesLength]
    have hdrawsMem : ∀ a ∈ draws, a ∈ A := by
      intro a ha
      have hmemW : a ∈ W := by
        rw [hW]
        exact List.mem_toFinset.mpr ha
      exact hWsubset hmemW
    have hformula' : ∀ b ∈ activeVertices n I.activeB,
        mapped b = writeClassReps sorted I.repClass 0 repValues (label b) := by
      intro b hb
      obtain ⟨hbN, hbActive⟩ := mem_activeVertices.mp hb
      exact hformula b hbN hbActive
    have hrepMem : ∀ b ∈ activeVertices n I.activeB,
        mapped b ∈ activeVertices n I.activeB := by
      intro b hb
      have hbN : b < n := (mem_activeVertices.mp hb).1
      have hbActive : I.activeB b = 1 := (mem_activeVertices.mp hb).2
      have hmem : mapped b ∈ xs := (hrepClass b hbN hbActive).2.1
      have hmem' : mapped b ∈ xs.toFinset := List.mem_toFinset.mpr hmem
      rw [hxs] at hmem'
      exact hmem'
    have hrepLabel : ∀ b ∈ activeVertices n I.activeB,
        label (mapped b) = label b := by
      intro b hb
      have hbN : b < n := (mem_activeVertices.mp hb).1
      have hbActive : I.activeB b = 1 := (mem_activeVertices.mp hb).2
      exact (hrepClass b hbN hbActive).2.2
    have hclasses' : ∀ b ∈ activeVertices n I.activeB,
        ∀ b' ∈ activeVertices n I.activeB,
          (label b = label b' ↔
            trace (numericNeighborhood G) W b =
              trace (numericNeighborhood G) W b') := hclasses
    obtain ⟨choice, hchoiceDraws, hchoiceSample, hchoiceRep⟩ :=
      initialChoice_of_actual draws W label mapped
        (fun d => writeClassReps sorted I.repClass 0 repValues d)
        hdrawsLength hdrawsMem (by simpa [draws] using hW)
        hclasses' hrepMem hrepLabel hformula'
    refine ⟨choice, hchoiceDraws, hchoiceSample, ?_⟩
    intro b hb
    exact hchoiceRep b hb

end Lax457868Proofs.InitialSamplerChoice
