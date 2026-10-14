import Mathlib.Tactic
import Lax457868Proofs.SamplerContract

/-!
Deduplicating vertices with identical neighborhoods preserves the set system
and its trace growth, while removing twins from the finite index family.
-/

namespace Lax457868Proofs.SamplerTwinSuppression

open Lax457868Proofs.SamplerContract
open Lax457868Proofs.SamplerPhases

variable {α β : Type*} [DecidableEq α]

/-- Every distinct neighborhood label is contained in the ground set when all
source vertices have neighborhoods contained there. -/
lemma image_neighborhoods_subset_of
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (hN : ∀ b ∈ B, N b ⊆ A) :
    ∀ T ∈ B.image N, T ⊆ A := by
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨b, hb, rfl⟩
  exact hN b hb

/-- The identity map is injective on the deduplicated neighborhood labels. -/
lemma id_injective_on_neighborhoods
    (B : Finset β) (N : β → Finset α) :
    ∀ ⦃T U : Finset α⦄, T ∈ B.image N → U ∈ B.image N →
      id T = id U → T = U := by
  intro T U _ _ h
  exact h

/-- Reindexing by distinct neighborhood labels leaves the public set system
unchanged, even when many vertices of `B` are twins. -/
lemma neighborhoodFamily_eq_deduplicated
    (B : Finset β) (N : β → Finset α) :
    neighborhoodFamily B N = neighborhoodFamily (B.image N) id := by
  ext X
  constructor
  · rintro ⟨b, hb, hEq⟩
    refine ⟨N b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    simpa using hEq
  · rintro ⟨T, hT, hEq⟩
    rcases Finset.mem_image.mp hT with ⟨b, hb, rfl⟩
    exact ⟨b, hb, by simpa using hEq⟩

/-- The internal refined-sample contract can be checked on distinct labels and
then read back for the original, possibly twin-heavy, vertex family. -/
lemma refinedSample_iff_deduplicated
    (A W : Finset α) (C : Finset β) (N : β → Finset α) (m k : ℕ) :
    Lax457868Proofs.RefinedSampleSpec.IsRefinedSample
      (neighborhoodFamily C N) (A : Set α) (W : Set α) m k ↔
    Lax457868Proofs.RefinedSampleSpec.IsRefinedSample
      (neighborhoodFamily (C.image N) id) (A : Set α) (W : Set α) m k := by
  rw [neighborhoodFamily_eq_deduplicated C N]

/-- The trace classes of the original vertex family are exactly the trace
classes of its distinct neighborhood labels. -/
lemma traceClasses_eq_deduplicated
    (B : Finset β) (N : β → Finset α) (Y : Finset α) :
    traceClasses id Y (B.image N) = traceClasses N Y B := by
  unfold traceClasses
  rw [Finset.image_image]
  apply Finset.image_congr
  intro b hb
  rfl

/-- If each neighborhood is contained in `A`, tracing the deduplicated labels
on all of `A` recovers the labels themselves. -/
lemma traceClasses_id_full_eq
    (A : Finset α) (B : Finset β) (N : β → Finset α)
    (hN : ∀ b ∈ B, N b ⊆ A) :
    traceClasses id A (B.image N) = B.image N := by
  unfold traceClasses
  rw [Finset.image_image]
  apply Finset.image_congr
  intro b hb
  have hTA : N b ⊆ A := hN b hb
  simp [trace, Finset.inter_eq_left.mpr hTA]

/-- Any linear trace bound on the original family transfers unchanged to the
deduplicated labels for every nonempty `Y ⊆ A`. -/
lemma deduplicated_trace_bound_of_trace_bound
    (A : Finset α) (B : Finset β) (N : β → Finset α) (c : ℕ)
    (htrace : ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses N Y B).card ≤ c * Y.card) :
    ∀ Y : Finset α, Y ⊆ A → Y.Nonempty →
      (traceClasses id Y (B.image N)).card ≤ c * Y.card := by
  intro Y hYA hY
  rw [traceClasses_eq_deduplicated B N Y]
  exact htrace Y hYA hY

/-- The full-ground-set trace bound gives a size bound on the number of
*distinct* neighborhoods, without any bound on the original `B.card`. -/
lemma deduplicated_neighborhoods_card_le
    (A : Finset α) (B : Finset β) (N : β → Finset α) (c : ℕ)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (htraceA : (traceClasses N A B).card ≤ c * A.card) :
    (B.image N).card ≤ c * A.card := by
  have hclasses : traceClasses id A (B.image N) = B.image N :=
    traceClasses_id_full_eq A B N hN
  rw [← hclasses, traceClasses_eq_deduplicated B N A]
  exact htraceA

end Lax457868Proofs.SamplerTwinSuppression
