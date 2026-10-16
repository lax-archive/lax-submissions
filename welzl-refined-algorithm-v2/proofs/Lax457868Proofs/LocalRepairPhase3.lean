import Lax457868Proofs.InitialSamplerChoice
import Lax457868Proofs.SamplerPhases

/-! Proof-side adapters connecting accepted local trials to the established
finite phase-three sampler. -/

namespace Lax457868Proofs.LocalRepairPhase3

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.InitialSamplerChoice

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Restricting neighborhoods to `A` preserves the isolation predicate when
both the base sample and the trial draws lie in `A`. -/
lemma localTrialIsolates_restricted_iff
    (N : β → Finset α) (B : Finset β) {A W : Finset α}
    (hWA : W ⊆ A) (b : β) (draws : List α)
    (hdraw : draws.toFinset ⊆ A) :
    localTrialIsolates N B W b draws ↔
      localTrialIsolates (fun v => N v ∩ A) B W b draws := by
  have hwhole : W ∪ draws.toFinset ⊆ A := Finset.union_subset hWA hdraw
  constructor <;> intro hiso v hv htrace hvb
  · have htrace' : trace N W b = trace N W v := by
      rw [restrictedNeighborhood_trace_eq N hWA b,
        restrictedNeighborhood_trace_eq N hWA v] at htrace
      exact htrace
    have hneq := hiso v hv htrace' hvb
    intro heq
    apply hneq
    calc
      trace N (W ∪ draws.toFinset) b =
          trace (fun x => N x ∩ A) (W ∪ draws.toFinset) b :=
        (restrictedNeighborhood_trace_eq N hwhole b).symm
      _ = trace (fun x => N x ∩ A) (W ∪ draws.toFinset) v := heq
      _ = trace N (W ∪ draws.toFinset) v :=
        restrictedNeighborhood_trace_eq N hwhole v
  · have htrace' : trace (fun x => N x ∩ A) W b =
        trace (fun x => N x ∩ A) W v := by
      rw [restrictedNeighborhood_trace_eq N hWA b,
        restrictedNeighborhood_trace_eq N hWA v]
      exact htrace
    have hneq := hiso v hv htrace' hvb
    intro heq
    apply hneq
    calc
      trace (fun x => N x ∩ A) (W ∪ draws.toFinset) b =
          trace N (W ∪ draws.toFinset) b :=
        restrictedNeighborhood_trace_eq N hwhole b
      _ = trace N (W ∪ draws.toFinset) v := heq
      _ = trace (fun x => N x ∩ A) (W ∪ draws.toFinset) v :=
        (restrictedNeighborhood_trace_eq N hwhole v).symm

/-- A single accepted local trial is exactly the successful singleton input
to the existing phase-three repair. -/
lemma phase3Repair_singleton_of_isolates
    (N : β → Finset α) (B : Finset β) (phaseTwoW accumulator : Finset α)
    (b rep : β) (k s : ℕ)
    (trial : LocalTrial ((N b \ N rep) ∪ (N rep \ N b)) s)
    (hfar : 2 * k < 3 * disagreement N b rep)
    (hiso : localTrialIsolates N B phaseTwoW b trial.draws) :
    phase3Repair N B phaseTwoW accumulator b rep k s [trial] =
      some (accumulator ∪ trial.draws.toFinset) := by
  have hok : localTrialIsolatesB N B phaseTwoW b trial.draws = true :=
    (localTrialIsolatesB_eq_true_iff N B phaseTwoW b trial.draws).2 hiso
  simp [phase3Repair, hfar, firstIsolatingTrial, hok]

private lemma phase3Scan_update_eq_of_not_mem
    (N : β → Finset α) (B : Finset β) (representative : β → β)
    (k s : ℕ)
    (trials : ∀ x : β, List (LocalTrial
      ((N x \ N (representative x)) ∪
        (N (representative x) \ N x)) s))
    (b : β) (replacement : List (LocalTrial
      ((N b \ N (representative b)) ∪
        (N (representative b) \ N b)) s)) :
    ∀ (order : List β) (hnot : b ∉ order) (phaseTwoW accumulator : Finset α),
      phase3Scan N B representative k s (Function.update trials b replacement)
          order phaseTwoW accumulator =
        phase3Scan N B representative k s trials order phaseTwoW accumulator := by
  intro order
  induction order with
  | nil => intros; rfl
  | cons x xs ih =>
      intro hnot phaseTwoW accumulator
      have hxb : x ≠ b := by
        intro h
        subst x
        exact hnot (by simp)
      have htailnot : b ∉ xs := by
        intro hm
        exact hnot (List.mem_cons_of_mem x hm)
      cases hstep : phase3Repair N B phaseTwoW accumulator x
          (representative x) k s (trials x) with
      | none => simp [phase3Scan, Function.update_of_ne hxb, hstep]
      | some next =>
          simp [phase3Scan, Function.update_of_ne hxb, hstep,
            ih htailnot phaseTwoW next]

/-- Glue a successful head repair to a successful tail scan, recording the
head trial as its singleton witness while preserving the tail witnesses. -/
lemma phase3Scan_prepend_trials
    (N : β → Finset α) (B : Finset β) (representative : β → β)
    (k s : ℕ)
    (trials : ∀ x : β, List (LocalTrial
      ((N x \ N (representative x)) ∪
        (N (representative x) \ N x)) s))
    (b : β) (tail : List β) (hnot : b ∉ tail)
    (phaseTwoW accumulator Wmid Wfinal : Finset α)
    (headTrials : List (LocalTrial
      ((N b \ N (representative b)) ∪
        (N (representative b) \ N b)) s))
    (hhead : phase3Repair N B phaseTwoW accumulator b (representative b)
      k s headTrials = some Wmid)
    (htail : phase3Scan N B representative k s trials tail phaseTwoW Wmid =
      some Wfinal) :
    ∃ trialFamily, trialFamily b = headTrials ∧
      (∀ x, x ≠ b → trialFamily x = trials x) ∧
      phase3Scan N B representative k s trialFamily (b :: tail)
        phaseTwoW accumulator = some Wfinal := by
  let trialFamily := Function.update trials b headTrials
  have hb : trialFamily b = headTrials := by
    simp [trialFamily]
  have htail' : phase3Scan N B representative k s trialFamily tail
      phaseTwoW Wmid = some Wfinal := by
    rw [phase3Scan_update_eq_of_not_mem N B representative k s trials b
      headTrials tail hnot phaseTwoW Wmid]
    exact htail
  refine ⟨trialFamily, hb, ?_, ?_⟩
  · intro x hxb
    simp [trialFamily, hxb]
  · simp [phase3Scan, hb, hhead, htail']

end Lax457868Proofs.LocalRepairPhase3
