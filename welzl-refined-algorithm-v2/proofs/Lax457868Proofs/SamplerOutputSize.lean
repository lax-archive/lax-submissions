import Lax457868Proofs.SamplerPhases
import Lax457868Proofs.SamplerRefinementBudget
import Lax457868Proofs.SamplerSize
import Mathlib.Tactic

/-!
Output containment and size bounds for the sampler's actual finite trials
and repair scans.
-/

namespace Lax457868Proofs.SamplerOutputSize

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerRefinementBudget
open Lax457868Proofs.SamplerSize

variable {α β : Type*} [DecidableEq α]

/-- The underlying set of a legal local trial stays inside the chosen
symmetric difference. -/
lemma localTrial_drawSet_subset {X : Finset α} {s : ℕ}
    (trial : LocalTrial X s) : trial.draws.toFinset ⊆ X := by
  intro a ha
  exact trial.draws_mem a (List.mem_toFinset.mp ha)

/-- Repeated draws can only reduce the cardinality of a local trial's
underlying set. -/
lemma localTrial_drawSet_card_le {X : Finset α} {s : ℕ}
    (trial : LocalTrial X s) : trial.draws.toFinset.card ≤ s := by
  calc
    trial.draws.toFinset.card ≤ trial.draws.length := List.toFinset_card_le _
    _ = s := trial.draws_length

/-- Any successful first-isolating-trial search returns the underlying set of
a legal trial, so its drawset lies in the prescribed difference and has at
most `s` elements. -/
lemma firstIsolatingTrial_output_bound (N : β → Finset α) (B : Finset β)
    [DecidableEq β]
    (W : Finset α) (b : β) (X : Finset α) (s : ℕ)
    (trials : List (LocalTrial X s)) (drawSet : Finset α)
    (hret : firstIsolatingTrial N B W b X s trials = some drawSet) :
    drawSet ⊆ X ∧ drawSet.card ≤ s := by
  obtain ⟨trial, _, hdraw, _⟩ :=
    firstIsolatingTrial_sound N B W b X s trials drawSet hret
  constructor
  · rw [← hdraw]
    exact localTrial_drawSet_subset trial
  · rw [← hdraw]
    exact localTrial_drawSet_card_le trial

/-- A nodup list that enumerates a finite set has length equal to that set's
cardinality. -/
lemma enum_length_eq_card {E : Finset β} [DecidableEq β] (order : List β)
    (hnodup : order.Nodup) (henum : order.toFinset = E) :
    order.length = E.card := by
  calc
    order.length = order.toFinset.card :=
      (List.toFinset_card_of_nodup hnodup).symm
    _ = E.card := congrArg Finset.card henum

/-- Phase two keeps its sample inside the ground set when every scanned
vertex and the starting sample lie there. -/
lemma phase2Scan_subset_of_ground (N : β → Finset α) (E : Finset β)
    [DecidableEq β]
    (A : Finset α) (as : List α) (W : Finset α)
    (hW : W ⊆ A) (has : ∀ a ∈ as, a ∈ A) :
    phase2Scan N E as W ⊆ A := by
  induction as generalizing W with
  | nil => exact hW
  | cons head rest ih =>
      have hrest : ∀ x ∈ rest, x ∈ A := by
        intro x hx
        exact has x (List.mem_cons_of_mem head hx)
      have hstep : phase2Step N E W head ⊆ A := by
        by_cases hs : splitsExceptionPairB N E W head = true
        · intro x hx
          simp [phase2Step, hs] at hx
          rcases hx with hxa | hx
          · subst x
            exact has head List.mem_cons_self
          · exact hW hx
        · simpa [phase2Step, hs] using hW
      exact ih (phase2Step N E W head) hstep hrest

/-- The symmetric difference of two neighborhoods contained in the ground set
is itself contained in the ground set. -/
lemma neighborhood_disagreement_subset (N : β → Finset α) (A : Finset α)
    (b rep : β) (hb : N b ⊆ A) (hrep : N rep ⊆ A) :
    (N b \ N rep) ∪ (N rep \ N b) ⊆ A := by
  intro a ha
  simp only [Finset.mem_union, Finset.mem_sdiff] at ha
  rcases ha with ⟨ha, _⟩ | ⟨ha, _⟩
  · exact hb ha
  · exact hrep ha

/-- A successful local repair returns the accumulator together with at most
`s` legal vertices from the exception's neighborhood disagreement. -/
lemma phase3Repair_output_bound (N : β → Finset α) (B : Finset β)
    [DecidableEq β]
    (A phaseTwoW accumulator : Finset α) (b rep : β) (k s : ℕ)
    (trials : List (LocalTrial ((N b \ N rep) ∪ (N rep \ N b)) s))
    (hacc : accumulator ⊆ A) (hNb : N b ⊆ A) (hNrep : N rep ⊆ A)
    (out : Finset α)
    (hret : phase3Repair N B phaseTwoW accumulator b rep k s trials = some out) :
    out ⊆ A ∧ out.card ≤ accumulator.card + s := by
  classical
  by_cases hfar : 2 * k < 3 * disagreement N b rep
  · let X := (N b \ N rep) ∪ (N rep \ N b)
    cases htrial : firstIsolatingTrial N B phaseTwoW b X s trials with
    | none => simp [phase3Repair, hfar, X, htrial] at hret
    | some drawSet =>
        simp [phase3Repair, hfar, X, htrial] at hret
        cases hret
        obtain ⟨hdrawsub, hdrawcard⟩ :=
          firstIsolatingTrial_output_bound N B phaseTwoW b X s trials drawSet htrial
        have hXsub : X ⊆ A := by
          exact neighborhood_disagreement_subset N A b rep hNb hNrep
        have hdrawA : drawSet ⊆ A := hdrawsub.trans hXsub
        constructor
        · exact Finset.union_subset hacc hdrawA
        · calc
            (accumulator ∪ drawSet).card ≤ accumulator.card + drawSet.card :=
              Finset.card_union_le _ _
            _ ≤ accumulator.card + s := Nat.add_le_add_left hdrawcard _
  · simp [phase3Repair, hfar] at hret
    cases hret
    exact ⟨hacc, by omega⟩

/-- A successful phase-three scan stays in the ground set and adds at most
`s` elements per entry of its exception order. -/
lemma phase3Scan_output_bound (N : β → Finset α) (B : Finset β)
    (A : Finset α)
    [DecidableEq β]
    (representative : β → β) (k s : ℕ)
    (trials : ∀ b : β, List (LocalTrial
      ((N b \ N (representative b)) ∪
        (N (representative b) \ N b)) s))
    (order : List β) (phaseTwoW accumulator : Finset α)
    (hacc : accumulator ⊆ A)
    (hN : ∀ b ∈ order,
      N b ⊆ A ∧ N (representative b) ⊆ A)
    (out : Finset α)
    (hret : phase3Scan N B representative k s trials order
      phaseTwoW accumulator = some out) :
    out ⊆ A ∧ out.card ≤ accumulator.card + s * order.length := by
  induction order generalizing accumulator with
  | nil =>
      simp [phase3Scan] at hret
      cases hret
      exact ⟨hacc, by simp⟩
  | cons b rest ih =>
      have hNrest : ∀ v ∈ rest,
          N v ⊆ A ∧ N (representative v) ⊆ A := by
        intro v hv
        exact hN v (List.mem_cons_of_mem b hv)
      obtain ⟨hbN, hbrepN⟩ := hN b List.mem_cons_self
      cases hstep : phase3Repair N B phaseTwoW accumulator b
          (representative b) k s (trials b) with
      | none =>
          simp [phase3Scan, hstep] at hret
      | some accumulator' =>
          have hretRest : phase3Scan N B representative k s trials rest
              phaseTwoW accumulator' = some out := by
            simpa [phase3Scan, hstep] using hret
          have hstepBound := phase3Repair_output_bound N B A phaseTwoW
            accumulator b (representative b) k s (trials b) hacc hbN hbrepN
            accumulator' hstep
          obtain ⟨hout, hcard⟩ :=
            ih accumulator' hstepBound.1 hNrest hretRest
          refine ⟨hout, ?_⟩
          calc
            out.card ≤ accumulator'.card + s * rest.length := hcard
            _ ≤ (accumulator.card + s) + s * rest.length :=
              Nat.add_le_add_right hstepBound.2 _
            _ = accumulator.card + s * (b :: rest).length := by
              simp [Nat.mul_add]
              omega

/-- Every successful three-phase run is contained in the ground set. Its
output size is bounded by the refined-sampler ceiling when the initial and
exception caps use the paper's floor quotients. -/
lemma runThreePhases_output_bound
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    [DecidableEq β] (r cap k s c : ℕ)
    (initialAttempts : List (InitialChoice A B N r))
    (groundOrder : List α) (groundOrder_finset : groundOrder.toFinset = A)
    (groundOrder_nodup : groundOrder.Nodup)
    (repairTrials : ∀ choice : InitialChoice A B N r, ∀ b : β,
      List (LocalTrial
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)) s))
    (exceptionOrder : ∀ choice : InitialChoice A B N r, List β)
    (exceptionOrder_finset : ∀ choice,
      (exceptionOrder choice).toFinset = choice.exceptions k)
    (exceptionOrder_nodup : ∀ choice, (exceptionOrder choice).Nodup)
    (hc : 0 < c)
    (hr : r = A.card / (4 * c ^ 2))
    (hcap : cap = A.card / (4 * c ^ 2 * (s + 1)))
    (hN : ∀ b ∈ B, N b ⊆ A)
    (out : Finset α)
    (hret : runThreePhases A B N r cap k s initialAttempts
      groundOrder groundOrder_finset groundOrder_nodup repairTrials
      exceptionOrder exceptionOrder_finset exceptionOrder_nodup = some out) :
    out ⊆ A ∧ out.card ≤ (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2) := by
  classical
  cases hchoice : chooseInitialAttempt initialAttempts k cap with
  | none =>
      simp [runThreePhases, hchoice] at hret
  | some choice =>
      have haccepted : (choice.exceptions k).card ≤ cap :=
        chooseInitialAttempt_sound initialAttempts k cap choice hchoice
      let E := choice.exceptions k
      let W₂ := phase2Scan N E groundOrder choice.sample
      have hrun : phase3Scan N B choice.representative k s
          (repairTrials choice) (exceptionOrder choice) W₂ W₂ = some out := by
        simpa [runThreePhases, hchoice, E, W₂] using hret
      have hsample : choice.sample.card ≤ r := by
        change choice.draws.toFinset.card ≤ r
        calc
          choice.draws.toFinset.card ≤ choice.draws.length := List.toFinset_card_le _
          _ = r := choice.draws_length
      have hsampleA : choice.sample ⊆ A := by
        intro a ha
        exact choice.draws_mem a (List.mem_toFinset.mp ha)
      have hground : ∀ a ∈ groundOrder, a ∈ A := by
        intro a ha
        have ha' : a ∈ groundOrder.toFinset := List.mem_toFinset.mpr ha
        rw [groundOrder_finset] at ha'
        exact ha'
      have hW₂A : W₂ ⊆ A := by
        exact phase2Scan_subset_of_ground N E A groundOrder choice.sample
          hsampleA hground
      have hW₂card : W₂.card ≤ choice.sample.card + E.card := by
        exact phase2Scan_card_add_le N E groundOrder choice.sample
      have hEsub : E ⊆ B := by
        intro b hb
        exact (Finset.mem_filter.mp hb).1
      have hNorder : ∀ b ∈ exceptionOrder choice,
          N b ⊆ A ∧ N (choice.representative b) ⊆ A := by
        intro b hb
        have hbE : b ∈ E := by
          change b ∈ choice.exceptions k
          rw [← exceptionOrder_finset choice]
          exact List.mem_toFinset.mpr hb
        have hbB : b ∈ B := hEsub hbE
        have hrepB : choice.representative b ∈ B :=
          choice.representative_mem b hbB
        exact ⟨hN b hbB, hN (choice.representative b) hrepB⟩
      have hscan : out ⊆ A ∧
          out.card ≤ W₂.card + s * (exceptionOrder choice).length := by
        exact phase3Scan_output_bound N B A choice.representative k s
          (repairTrials choice) (exceptionOrder choice) W₂ W₂ hW₂A
          hNorder out hrun
      have horderlen : (exceptionOrder choice).length = E.card := by
        simpa [E] using enum_length_eq_card (exceptionOrder choice)
          (exceptionOrder_nodup choice) (exceptionOrder_finset choice)
      have hq : E.card ≤ cap := by
        exact haccepted
      have hDcap :
          (4 * c ^ 2 * (s + 1)) * cap ≤ A.card := by
        calc
          (4 * c ^ 2 * (s + 1)) * cap =
              (4 * c ^ 2 * (s + 1)) *
                (A.card / (4 * c ^ 2 * (s + 1))) := by rw [hcap]
          _ = (A.card / (4 * c ^ 2 * (s + 1))) *
              (4 * c ^ 2 * (s + 1)) := Nat.mul_comm _ _
          _ ≤ A.card := Nat.div_mul_le_self _ _
      have hbudget : 4 * c ^ 2 * (s + 1) * E.card ≤ A.card := by
        calc
          4 * c ^ 2 * (s + 1) * E.card =
              (4 * c ^ 2 * (s + 1)) * E.card := by ring
          _ ≤ (4 * c ^ 2 * (s + 1)) * cap :=
            Nat.mul_le_mul_left _ hq
          _ ≤ A.card := hDcap
      have hbound := sampler_budget_output_bound A.card c s E.card hc hbudget
      refine ⟨hscan.1, ?_⟩
      calc
        out.card ≤ W₂.card + s * E.card := by
          simpa [horderlen] using hscan.2
        _ ≤ (choice.sample.card + E.card) + s * E.card :=
          Nat.add_le_add_right hW₂card _
        _ ≤ r + E.card + s * E.card := by omega
        _ = A.card / (4 * c ^ 2) + E.card + s * E.card := by rw [hr]
        _ ≤ (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2) := by
          exact hbound

/-- The public finite-choice sampler always returns a set inside the ground
set and obeys the paper's refined-sampler size ceiling, including the two
immediate empty-output branches. -/
lemma refinedSampler_output_bound
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    [DecidableEq β] (r cap k s c : ℕ)
    (initialAttempts : List (InitialChoice A B N r))
    (groundOrder : List α) (groundOrder_finset : groundOrder.toFinset = A)
    (groundOrder_nodup : groundOrder.Nodup)
    (repairTrials : ∀ choice : InitialChoice A B N r, ∀ b : β,
      List (LocalTrial
        ((N b \ N (choice.representative b)) ∪
          (N (choice.representative b) \ N b)) s))
    (exceptionOrder : ∀ choice : InitialChoice A B N r, List β)
    (exceptionOrder_finset : ∀ choice,
      (exceptionOrder choice).toFinset = choice.exceptions k)
    (exceptionOrder_nodup : ∀ choice, (exceptionOrder choice).Nodup)
    (hc : 0 < c)
    (hr : r = A.card / (4 * c ^ 2))
    (hcap : cap = A.card / (4 * c ^ 2 * (s + 1)))
    (hN : ∀ b ∈ B, N b ⊆ A)
    (out : Finset α)
    (hret : refinedSampler A B N r cap k s initialAttempts groundOrder
      groundOrder_finset groundOrder_nodup repairTrials exceptionOrder
      exceptionOrder_finset exceptionOrder_nodup = some out) :
    out ⊆ A ∧ out.card ≤ (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2) := by
  classical
  by_cases hstop : A.card ≤ k ∨ B = ∅
  · simp [refinedSampler, hstop] at hret
    cases hret
    constructor
    · exact Finset.empty_subset A
    · simp
  · have hrun : runThreePhases A B N r cap k s initialAttempts groundOrder
        groundOrder_finset groundOrder_nodup repairTrials exceptionOrder
        exceptionOrder_finset exceptionOrder_nodup = some out := by
      simpa [refinedSampler, hstop] using hret
    exact runThreePhases_output_bound A B N r cap k s c initialAttempts
      groundOrder groundOrder_finset groundOrder_nodup repairTrials
      exceptionOrder exceptionOrder_finset exceptionOrder_nodup hc hr hcap
      hN out hrun

end Lax457868Proofs.SamplerOutputSize
