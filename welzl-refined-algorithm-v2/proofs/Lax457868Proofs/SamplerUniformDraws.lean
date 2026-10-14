import Mathlib.Tactic
import Lax457868Proofs.SamplerPhases

/-!
The finite probability space for a local repair: an ordered tape of `s`
independent draws from `X`, with replacement.  Uniform probability is the
counting measure on these tapes.
-/

namespace Lax457868Proofs.SamplerUniformDraws

open Lax457868Proofs.SamplerPhases

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- One length-`s` ordered tape of draws from `X`. -/
abbrev Tape (X : Finset α) (s : ℕ) := Fin s → {a // a ∈ X}

/-- A tape misses `D` when none of its positions lies in `D`. -/
def Misses (D : Finset α) {X : Finset α} {s : ℕ} (tape : Tape X s) : Prop :=
  ∀ i, (tape i).val ∉ D

noncomputable instance missesDecidable (D : Finset α) {X : Finset α} {s : ℕ} :
    DecidablePred (Misses D : Tape X s → Prop) := fun _ => Classical.propDecidable _

/-- Turn a tape into the ordered list consumed by `LocalTrial`. -/
def Tape.toList {X : Finset α} {s : ℕ} (tape : Tape X s) : List α :=
  List.ofFn fun i : Fin s => (tape i).val

lemma Tape.toList_length {X : Finset α} {s : ℕ} (tape : Tape X s) :
    tape.toList.length = s := by
  simp [Tape.toList]

lemma Tape.toList_mem {X : Finset α} {s : ℕ} (tape : Tape X s)
    {a : α} (ha : a ∈ tape.toList) : a ∈ X := by
  simp only [Tape.toList, List.mem_ofFn] at ha
  rcases ha with ⟨i, rfl⟩
  exact (tape i).property

/-- Every tape induces a legal `LocalTrial` with the same length and draw set. -/
def Tape.toLocalTrial {X : Finset α} {s : ℕ} (tape : Tape X s) : LocalTrial X s where
  draws := tape.toList
  draws_length := tape.toList_length
  draws_mem := fun a ha => tape.toList_mem ha

/-- Tapes that miss `D` are exactly functions into the part of `X` outside
`D`. -/
def missEquiv (X D : Finset α) (s : ℕ) :
    {tape : Tape X s // Misses D tape} ≃
      (Fin s → {a // a ∈ X.filter (fun a => a ∉ D)}) where
  toFun tape i := ⟨(tape.1 i).val, by
    simp only [Finset.mem_filter]
    exact ⟨(tape.1 i).property, tape.2 i⟩⟩
  invFun f := ⟨fun i => ⟨(f i).val, (Finset.mem_filter.mp (f i).property).1⟩,
    fun i => (Finset.mem_filter.mp (f i).property).2⟩
  left_inv tape := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv f := by
    funext i
    apply Subtype.ext
    rfl

/-- The number of ordered length-`s` tapes from `X` that miss `D` is exactly
`(|X \ D|)^s`. This is a count, independent of any probability axioms. -/
theorem card_miss_tapes (X D : Finset α) (s : ℕ) :
    Fintype.card {tape : Tape X s // Misses D tape} =
      (X.filter (fun a => a ∉ D)).card ^ s := by
  classical
  rw [Fintype.card_congr (missEquiv X D s)]
  simp [Fintype.card_fun]

/-- If `D` is a range inside the draw domain, its miss count is
`(|X| - |D|)^s`. -/
lemma card_miss_tapes_eq_sub_card (X D : Finset α) (s : ℕ)
    (hDX : D ⊆ X) :
    Fintype.card {tape : Tape X s // Misses D tape} = (X.card - D.card) ^ s := by
  rw [card_miss_tapes]
  have hfilter : X.filter (fun a => a ∉ D) = X \ D := by
    ext a
    simp [Finset.mem_sdiff]
  rw [hfilter, Finset.card_sdiff_of_subset hDX]

/-- The full finite sample space has `|X|^s` tapes, including repetitions. -/
lemma card_tapes (X : Finset α) (s : ℕ) :
    Fintype.card (Tape X s) = X.card ^ s := by
  classical
  simp [Tape, Fintype.card_fun]

/-- Each tape is equipped with the same counting weight; this names the
uniform experiment's denominator and numerator explicitly. -/
def sampleSpace (X : Finset α) (s : ℕ) : Finset (Tape X s) := Finset.univ

noncomputable def missSpace (X D : Finset α) (s : ℕ) : ℕ :=
  Fintype.card {tape : Tape X s // Misses D tape}

lemma card_sampleSpace (X : Finset α) (s : ℕ) :
    (sampleSpace X s).card = X.card ^ s := by
  classical
  simp [sampleSpace, card_tapes]

lemma card_missSpace (X D : Finset α) (s : ℕ) :
    missSpace X D s = (X.filter (fun a => a ∉ D)).card ^ s :=
  card_miss_tapes X D s

/-- The miss-space numerator has the usual `(|X|-|D|)^s` form when the
distinguishing range lies inside the draw domain. -/
lemma missSpace_eq_sub_card (X D : Finset α) (s : ℕ)
    (hDX : D ⊆ X) :
    missSpace X D s = (X.card - D.card) ^ s := by
  rw [card_missSpace]
  have hfilter : X.filter (fun a => a ∉ D) = X \ D := by
    ext a
    simp [Finset.mem_sdiff]
  rw [hfilter, Finset.card_sdiff_of_subset hDX]

end Lax457868Proofs.SamplerUniformDraws
