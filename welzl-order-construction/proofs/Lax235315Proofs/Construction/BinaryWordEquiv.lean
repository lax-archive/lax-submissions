import Lax235315Proofs.Construction.RandomBits
import Lax235315Proofs.Construction.RandomKeyEquiv
import Lax195003.WordRamRandomness
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! Exact finite equivalence for the source reader's big-endian bit words. -/

namespace Lax235315Proofs.Construction.BinaryWordEquiv

open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeyEquiv

noncomputable section

/-- The numeric source tape for a Boolean word, in the order consumed by the
literal reader. -/
def sourceWordBits {L : ℕ} (word : Fin L → Bool) : List ℕ := bitTape word

/-- The value read by `RandomBits.bitsValue` from the numeric source tape. -/
def sourceWordValue {L : ℕ} (word : Fin L → Bool) : ℕ :=
  bitsValue (sourceWordBits word)

lemma sourceWordValue_lt {L : ℕ} (word : Fin L → Bool) :
    sourceWordValue word < 2 ^ L := by
  simpa [sourceWordValue, sourceWordBits, bitTape] using
    (bitsValue_lt_pow (bitTape word) (fun b hb =>
      Nat.lt_succ_iff.mp (bitTape_bounded word b hb)))

/-- Boolean source words correspond exactly to the values read by the source
bit reader, viewed as elements of `Fin (2^L)`. -/
def sourceWordEquiv (L : ℕ) : (Fin L → Bool) ≃ Fin (2 ^ L) := by
  let f : (Fin L → Bool) → Fin (2 ^ L) := fun word =>
    ⟨sourceWordValue word, sourceWordValue_lt word⟩
  have hinj : Function.Injective f := by
    intro word₁ word₂ h
    apply boolWordValue_injective
    have hv := congrArg Fin.val h
    simpa [f, sourceWordValue, sourceWordBits, boolWordValue] using hv
  have hcard : Fintype.card (Fin L → Bool) = Fintype.card (Fin (2 ^ L)) := by
    simp
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)

/-- The equivalence's numeric value is exactly what the source reader reads. -/
@[simp] lemma sourceWordEquiv_val {L : ℕ} (word : Fin L → Bool) :
    (sourceWordEquiv L word).val = bitsValue (sourceWordBits word) := by
  rfl

/-- Source words whose read value belongs to a specified finite event. -/
def eventPreimage {L : ℕ} (event : Finset (Fin (2 ^ L))) :
    Finset (Fin L → Bool) :=
  Finset.univ.filter fun word => sourceWordEquiv L word ∈ event

/-- The exact word/value equivalence preserves the cardinality of every
finite event under preimage, including the zero-bit case. -/
lemma card_eventPreimage {L : ℕ} (event : Finset (Fin (2 ^ L))) :
    (eventPreimage (L := L) event).card = event.card := by
  classical
  have himage : (eventPreimage (L := L) event).image (sourceWordEquiv L) = event := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨word, hword, rfl⟩
      exact (Finset.mem_filter.mp hword).2
    · intro hx
      refine Finset.mem_image.mpr ⟨(sourceWordEquiv L).symm x, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa using hx
      · simp
  calc
    (eventPreimage (L := L) event).card =
        ((eventPreimage (L := L) event).image (sourceWordEquiv L)).card := by
          rw [Finset.card_image_of_injective _ (sourceWordEquiv L).injective]
    _ = event.card := by rw [himage]

end

end Lax235315Proofs.Construction.BinaryWordEquiv
