import Lax457868Proofs.SamplerRefinementBudget
import Lax457868Proofs.ReusedOriginal.Construction.RefineOneSource

/-! A finite-label adapter connecting the reused numeric refinement engine to
the trace classes counted by phase two. -/

namespace Lax457868Proofs.ExceptionRefinementBridge

open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.SamplerRefinementBudget
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RefineSplitMath
open Lax457868Proofs.ReusedOriginal.Construction.RefineOneSource

variable {α : Type*} {E : Finset ℕ} [DecidableEq α]

lemma trace_insert_eq_iff (N : ℕ → Finset α) (W : Finset α) (a : α)
    (b b' : ℕ) :
    trace N (insert a W) b = trace N (insert a W) b' ↔
      trace N W b = trace N W b' ∧ (a ∈ N b ↔ a ∈ N b') := by
  by_cases haW : a ∈ W
  · rw [Finset.insert_eq_of_mem haW]
    constructor
    · intro h
      refine ⟨h, ?_⟩
      have hpoint := congrArg (fun T : Finset α => a ∈ T) h
      simpa [trace, haW] using hpoint
    · intro h
      exact h.1
  · constructor
    · intro h
      have hrestrict := congrArg (fun T : Finset α => T ∩ W) h
      have hrestrict' : trace N W b = trace N W b' := by
        simpa [trace_restrict (W := W) (W' := insert a W)
          (by intro x hx; exact Finset.mem_insert_of_mem hx)] using hrestrict
      have hpoint := congrArg (fun T : Finset α => a ∈ T) h
      have hpoint' : a ∈ N b ↔ a ∈ N b' := by
        simpa [trace, haW] using hpoint
      exact ⟨hrestrict', hpoint'⟩
    · rintro ⟨hW, ha⟩
      ext x
      simp only [trace, Finset.mem_inter, Finset.mem_insert]
      by_cases hx : x = a
      · subst x
        simpa [trace, haW] using ha
      · by_cases hxW : x ∈ W
        · have hpoint := congrArg (fun T : Finset α => x ∈ T) hW
          have hiff : (x ∈ N b ∧ x ∈ W) ↔ (x ∈ N b' ∧ x ∈ W) := by
            simpa [trace] using hpoint
          constructor
          · rintro ⟨hNb, _⟩
            exact ⟨(hiff.mp ⟨hNb, hxW⟩).1, Or.inr hxW⟩
          · rintro ⟨hNb', _⟩
            exact ⟨(hiff.mpr ⟨hNb', hxW⟩).1, Or.inr hxW⟩
        · simp [trace, hx, hxW]

/-- Compact numeric labels represent exactly the distinct traces on `E`.
The proof uses the finite image cardinality lemmas in both directions. -/
lemma classCount_eq_traceClasses_card
    (N : ℕ → Finset α) (W : Finset α) (label : ℕ → ℕ) (q : ℕ)
    (hrange : ∀ b ∈ E, label b < q)
    (hoccupied : LabelsOccupyPrefix q label E)
    (heq : ∀ b ∈ E, ∀ b' ∈ E,
      (label b = label b' ↔ trace N W b = trace N W b')) :
    q = (traceClasses N W E).card := by
  classical
  let labels := E.image label
  let traces := traceClasses N W E
  let toTrace (k : ℕ) : Finset α :=
    if hk : k ∈ labels then
      trace N W (Classical.choose (Finset.mem_image.mp hk))
    else ∅
  let toLabel (T : Finset α) : ℕ :=
    if hT : T ∈ traces then
      label (Classical.choose (Finset.mem_image.mp (by
        simpa [traces, traceClasses] using hT)))
    else 0
  have hlabels : labels = Finset.range q := by
    ext k
    constructor
    · intro hk
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (hrange b hb)
    · intro hk
      have hkq : k < q := Finset.mem_range.mp hk
      have hpos := hoccupied k hkq
      obtain ⟨b, hb, hbk⟩ := (mem_touchedClasses).mp
        ((classMultiplicity_pos_iff).mp hpos)
      exact Finset.mem_image.mpr ⟨b, hb, hbk⟩
  have htoTraceMaps : ∀ k ∈ labels, toTrace k ∈ traces := by
    intro k hk
    simp only [toTrace, dif_pos hk]
    exact Finset.mem_image.mpr ⟨Classical.choose (Finset.mem_image.mp hk),
      (Classical.choose_spec (Finset.mem_image.mp hk)).1, rfl⟩
  have htoTraceInj : Set.InjOn toTrace (labels : Set ℕ) := by
    intro k hk k' hk' hkk'
    have hrep := Classical.choose_spec (Finset.mem_image.mp hk)
    have hrep' := Classical.choose_spec (Finset.mem_image.mp hk')
    have hkF : k ∈ labels := by simpa using hk
    have hk'F : k' ∈ labels := by simpa using hk'
    have heqTrace : trace N W (Classical.choose (Finset.mem_image.mp hk)) =
        trace N W (Classical.choose (Finset.mem_image.mp hk')) := by
      simp only [toTrace, dif_pos hkF, dif_pos hk'F] at hkk'
      exact hkk'
    have heqLabel := (heq _ hrep.1 _ hrep'.1).2 heqTrace
    simpa [hrep.2, hrep'.2] using heqLabel
  have htoLabelMaps : ∀ T ∈ traces, toLabel T ∈ labels := by
    intro T hT
    have hmem : Classical.choose (Finset.mem_image.mp (by
        simpa [traces, traceClasses] using hT)) ∈ E :=
      (Classical.choose_spec (Finset.mem_image.mp (by
        simpa [traces, traceClasses] using hT))).1
    simp only [toLabel, dif_pos hT]
    exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  have htoLabelInj : Set.InjOn toLabel (traces : Set (Finset α)) := by
    intro T hT T' hT' hTT'
    have hb := Classical.choose_spec (Finset.mem_image.mp (by
      simpa [traces, traceClasses] using hT))
    have hb' := Classical.choose_spec (Finset.mem_image.mp (by
      simpa [traces, traceClasses] using hT'))
    have hTF : T ∈ traces := by simpa using hT
    have hT'F : T' ∈ traces := by simpa using hT'
    have hlabelsEq : label (Classical.choose (Finset.mem_image.mp (by
          simpa [traces, traceClasses] using hT))) =
        label (Classical.choose (Finset.mem_image.mp (by
          simpa [traces, traceClasses] using hT'))) := by
      simp only [toLabel, dif_pos hTF, dif_pos hT'F] at hTT'
      exact hTT'
    have htraceEq := (heq _ hb.1 _ hb'.1).1 hlabelsEq
    simpa [hb.2, hb'.2] using htraceEq
  have hcardLE : labels.card ≤ traces.card :=
    Finset.card_le_card_of_injOn toTrace htoTraceMaps htoTraceInj
  have hcardGE : traces.card ≤ labels.card :=
    Finset.card_le_card_of_injOn toLabel htoLabelMaps htoLabelInj
  have hcard : labels.card = traces.card := Nat.le_antisymm hcardLE hcardGE
  calc
    q = labels.card := by rw [hlabels]; simp
    _ = traces.card := hcard
    _ = (traceClasses N W E).card := rfl

/-- One-coordinate refinement increases the compact class count exactly when
the sampled point separates a pair of exceptions. The label equivalences are
the exact pairwise contract returned by `RefineOneSource.refineOne_run`. -/
lemma refinedClassCount_gt_iff_splits
    (N : ℕ → Finset α) (E : Finset ℕ) (W : Finset α) (a : α)
    (label newCount : ℕ → ℕ) (q q' : ℕ)
    (hrange : ∀ b ∈ E, label b < q)
    (hoccupied : LabelsOccupyPrefix q label E)
    (hlabel : ∀ b ∈ E, ∀ b' ∈ E,
      (label b = label b' ↔ trace N W b = trace N W b'))
    (hnewRange : ∀ b ∈ E, newCount b < q')
    (hnewOccupied : LabelsOccupyPrefix q' newCount E)
    (hrefine : ∀ b ∈ E, ∀ b' ∈ E,
      (newCount b = newCount b' ↔
        label b = label b' ∧ (a ∈ N b ↔ a ∈ N b'))) :
    q < q' ↔ splitsExceptionPair N E W a := by
  classical
  have hq := classCount_eq_traceClasses_card N W label q hrange hoccupied hlabel
  have hq' : q' = (traceClasses N (insert a W) E).card := by
    apply classCount_eq_traceClasses_card N (insert a W) newCount q'
    · exact hnewRange
    · exact hnewOccupied
    · intro b hb b' hb'
      rw [hrefine b hb b' hb']
      rw [hlabel b hb b' hb']
      exact (trace_insert_eq_iff N W a b b').symm
  rw [hq, hq']
  constructor
  · intro hgrowth
    by_contra hsplit
    have hno : ∀ b ∈ E, ∀ b' ∈ E,
        trace N W b = trace N W b' → (a ∈ N b ↔ a ∈ N b') := by
      intro b hb b' hb' htr
      by_contra hmem
      have hdiff : (a ∈ N b ∧ a ∉ N b') ∨ (a ∉ N b ∧ a ∈ N b') := by
        tauto
      exact hsplit ⟨b, b', hb, hb', htr, hdiff⟩
    let currentClasses := traceClasses N (insert a W) E
    let restrict := fun T : Finset α => T ∩ W
    have hrestrictImage : currentClasses.image restrict = traceClasses N W E :=
      traceClasses_restrict (E := E) (W := W) (W' := insert a W)
        (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have hrestrictInj : Set.InjOn restrict (currentClasses : Set (Finset α)) := by
      intro T hT T' hT' hrestrict
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hT'
      have htr : trace N W b = trace N W b' := by
        simpa [restrict, trace_restrict (W := W) (W' := insert a W)
          (by intro x hx; exact Finset.mem_insert_of_mem hx)] using hrestrict
      have hadj := hno b hb b' hb' htr
      exact (trace_insert_eq_iff N W a b b').2 ⟨htr, hadj⟩
    have hcard := Finset.card_image_of_injOn hrestrictInj
    rw [hrestrictImage] at hcard
    exact (Nat.not_lt_of_ge hcard.symm.le) hgrowth
  · exact traceClasses_card_lt_insert_of_split (N := N) E W a

/-- The sampler's phase-two step is exactly the compact-class-count test
implemented by the reused refinement pass. -/
lemma phase2Step_eq_if_refinedClassCount_gt
    (N : ℕ → Finset α) (E : Finset ℕ) (W : Finset α) (a : α)
    (label newCount : ℕ → ℕ) (q q' : ℕ)
    (hrange : ∀ b ∈ E, label b < q)
    (hoccupied : LabelsOccupyPrefix q label E)
    (hlabel : ∀ b ∈ E, ∀ b' ∈ E,
      (label b = label b' ↔ trace N W b = trace N W b'))
    (hnewRange : ∀ b ∈ E, newCount b < q')
    (hnewOccupied : LabelsOccupyPrefix q' newCount E)
    (hrefine : ∀ b ∈ E, ∀ b' ∈ E,
      (newCount b = newCount b' ↔
        label b = label b' ∧ (a ∈ N b ↔ a ∈ N b'))) :
    phase2Step N E W a = if q < q' then insert a W else W := by
  have hgrowth := refinedClassCount_gt_iff_splits N E W a label
    newCount q q' hrange hoccupied hlabel hnewRange hnewOccupied hrefine
  by_cases hs : splitsExceptionPair N E W a
  · have hbool : splitsExceptionPairB N E W a = true :=
      (splitsExceptionPairB_eq_true_iff N E W a).2 hs
    have hcount : q < q' := hgrowth.mpr hs
    simp [phase2Step, hbool, hcount]
  · have hbool : splitsExceptionPairB N E W a = false := by
      cases h : splitsExceptionPairB N E W a with
      | false => rfl
      | true => exact False.elim (hs ((splitsExceptionPairB_eq_true_iff N E W a).1 h))
    have hcount : ¬ q < q' := fun h => hs (hgrowth.mp h)
    simp [phase2Step, hbool, hcount]

end Lax457868Proofs.ExceptionRefinementBridge
