import Lax457868Proofs.SamplerPhases
import Mathlib.Tactic

/-!
The phase-two scan spends at most one new sample point for each increase in
the number of exception trace classes.  This bounds its actual output by the
number of initial exceptions.
-/

namespace Lax457868Proofs.SamplerRefinementBudget

open Lax457868Proofs.SamplerPhases

variable {α β : Type*} [DecidableEq α]

/-- Restricting a trace from a larger sample recovers the trace on a smaller
sample. -/
lemma trace_restrict {N : β → Finset α} {W W' : Finset α}
    (hWW' : W ⊆ W') (b : β) :
    trace N W' b ∩ W = trace N W b := by
  ext a
  simp only [trace, Finset.mem_inter]
  constructor
  · rintro ⟨⟨haN, haW'⟩, haW⟩
    exact ⟨haN, haW⟩
  · rintro ⟨haN, haW⟩
    exact ⟨⟨haN, hWW' haW⟩, haW⟩

/-- Every trace class on a smaller sample is the restriction of a trace class
on a larger sample. -/
lemma traceClasses_restrict {N : β → Finset α} {E : Finset β}
    {W W' : Finset α} (hWW' : W ⊆ W') :
    (traceClasses N W' E).image (fun T => T ∩ W) = traceClasses N W E := by
  unfold traceClasses
  rw [Finset.image_image]
  apply Finset.image_congr
  intro b hb
  exact trace_restrict hWW' b

/-- Adding sample elements cannot reduce the number of distinct traces. -/
lemma traceClasses_card_mono {N : β → Finset α} (E : Finset β)
    {W W' : Finset α} (hWW' : W ⊆ W') :
    (traceClasses N W E).card ≤ (traceClasses N W' E).card := by
  rw [← traceClasses_restrict hWW']
  exact Finset.card_image_le

/-- Adding one vertex that splits an equal-trace pair strictly increases the
number of exception trace classes. -/
lemma traceClasses_card_lt_insert_of_split {N : β → Finset α}
    (E : Finset β) (W : Finset α) (a : α)
    (hsplit : splitsExceptionPair N E W a) :
    (traceClasses N W E).card <
      (traceClasses N (insert a W) E).card := by
  classical
  rcases hsplit with ⟨b, b', hb, hb', htrace, hdiff⟩
  let W' := insert a W
  let newClasses := traceClasses N W' E
  let restrict := fun T : Finset α => T ∩ W
  have himage : newClasses.image restrict = traceClasses N W E := by
    exact traceClasses_restrict (E := E) (W := W) (W' := W')
      (by intro x hx; exact Finset.mem_insert_of_mem hx)
  have hmemB : trace N W' b ∈ newClasses := by
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hmemB' : trace N W' b' ∈ newClasses := by
    exact Finset.mem_image.mpr ⟨b', hb', rfl⟩
  have hrestrict : restrict (trace N W' b) = restrict (trace N W' b') := by
    dsimp [restrict]
    rw [trace_restrict (W := W) (W' := W') (by
      intro x hx
      exact Finset.mem_insert_of_mem hx) b,
      trace_restrict (W := W) (W' := W') (by
      intro x hx
      exact Finset.mem_insert_of_mem hx) b']
    exact htrace
  have hdistinct : trace N W' b ≠ trace N W' b' := by
    intro heq
    have hmem := congrArg (fun T : Finset α => a ∈ T) heq
    rcases hdiff with hdiff | hdiff
    · have hleft : a ∈ trace N W' b := by
        simp [trace, W', hdiff.1]
      have hright : a ∉ trace N W' b' := by
        simp [trace, W', hdiff.2]
      exact hright (hmem ▸ hleft)
    · have hleft : a ∉ trace N W' b := by
        simp [trace, W', hdiff.1]
      have hright : a ∈ trace N W' b' := by
        simp [trace, W', hdiff.2]
      exact hleft (hmem ▸ hright)
  have hnotinj : ¬ Set.InjOn restrict (↑newClasses : Set (Finset α)) := by
    intro hinj
    exact hdistinct (hinj hmemB hmemB' hrestrict)
  have hcard_ne :
      (newClasses.image restrict).card ≠ newClasses.card := by
    intro heq
    exact hnotinj ((Finset.card_image_iff).mp heq)
  have hle : (traceClasses N W E).card ≤ newClasses.card := by
    rw [← himage]
    exact Finset.card_image_le
  have hne : (traceClasses N W E).card ≠ newClasses.card := by
    intro heq
    exact hcard_ne (by simpa [himage] using heq)
  exact Nat.lt_of_le_of_ne hle hne

/-- One phase-two step increases the sample size by at most the increase in
the number of exception trace classes. -/
lemma phase2Step_potential (N : β → Finset α) (E : Finset β)
    (W : Finset α) (a : α) :
    (phase2Step N E W a).card + (traceClasses N W E).card ≤
      W.card + (traceClasses N (phase2Step N E W a) E).card := by
  classical
  by_cases hs : splitsExceptionPairB N E W a = true
  · have hsplit : splitsExceptionPair N E W a :=
      (splitsExceptionPairB_eq_true_iff N E W a).mp hs
    by_cases ha : a ∈ W
    · simp [phase2Step, hs, ha]
    · have hout : phase2Step N E W a = insert a W := by
        simp [phase2Step, hs]
      have hclasses := traceClasses_card_lt_insert_of_split
        (N := N) E W a hsplit
      rw [hout]
      have hsize : (insert a W).card ≤ W.card + 1 := Finset.card_insert_le a W
      omega
  · simp [phase2Step, hs]

/-- Across a complete phase-two scan, each added point is paid for by a
strict increase in the number of exception trace classes. -/
lemma phase2Scan_potential (N : β → Finset α) (E : Finset β)
    (as : List α) (W : Finset α) :
    (phase2Scan N E as W).card + (traceClasses N W E).card ≤
      W.card + (traceClasses N (phase2Scan N E as W) E).card := by
  induction as generalizing W with
  | nil => simp [phase2Scan]
  | cons a rest ih =>
      change (phase2Scan N E rest (phase2Step N E W a)).card +
          (traceClasses N W E).card ≤
        W.card + (traceClasses N (phase2Scan N E rest (phase2Step N E W a)) E).card
      have hstep := phase2Step_potential N E W a
      have htail := ih (phase2Step N E W a)
      omega

/-- A complete phase-two scan adds at most one sample vertex per initial
exception. -/
lemma phase2Scan_card_add_le (N : β → Finset α) (E : Finset β)
    (as : List α) (W : Finset α) :
    (phase2Scan N E as W).card ≤ W.card + E.card := by
  have hpotential := phase2Scan_potential N E as W
  have hclasses : (traceClasses N (phase2Scan N E as W) E).card ≤ E.card := by
    unfold traceClasses
    exact Finset.card_image_le
  omega

end Lax457868Proofs.SamplerRefinementBudget
