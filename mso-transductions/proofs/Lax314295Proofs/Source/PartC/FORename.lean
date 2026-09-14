/-
Renaming of variables and first-order formulas.

Auxiliary syntactic lemmas about `MSO.rename` and `MSO.shiftUp` of
`RequestProject/PartC/MSOSubst.lean`, used in Section *The first-order fragment*: renaming preserves
first-orderness and the quantifier rank, it acts on the variables of a formula
in the obvious way, and it does not change the meaning of a first-order
sentence.  Shifting a sentence up is the standard way of making a variable
fresh for it.
-/
import Lax314295Proofs.Source.PartC.MSOSubst
import Lax314295Proofs.Source.PartC.FORel
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace MSO

variable {A : Type}

lemma isFO_rename (r : ℕ → ℕ) : ∀ φ : MSO A, φ.IsFO → (rename r φ).IsFO := by
  intro φ
  induction φ with
  | le i j => exact fun _ => trivial
  | lab a i => exact fun _ => trivial
  | mem i j => exact fun h => h.elim
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | exFO i φ ih => exact ih
  | exSO i φ _ => exact fun h => h.elim

lemma isFO_shiftUp (d : ℕ) {φ : MSO A} (h : φ.IsFO) : (shiftUp d φ).IsFO :=
  isFO_rename _ φ h

lemma qrank_rename (r : ℕ → ℕ) : ∀ φ : MSO A, (rename r φ).qrank = φ.qrank := by
  intro φ
  induction φ with
  | le i j => rfl
  | lab a i => rfl
  | mem i j => rfl
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => exact congrArg₂ max ihφ ihψ
  | or φ ψ ihφ ihψ => exact congrArg₂ max ihφ ihψ
  | exFO i φ ih => exact congrArg (· + 1) ih
  | exSO i φ ih => exact congrArg (· + 1) ih

@[simp] lemma qrank_shiftUp (d : ℕ) (φ : MSO A) : (shiftUp d φ).qrank = φ.qrank :=
  qrank_rename _ φ

lemma foVars_rename (r : ℕ → ℕ) : ∀ φ : MSO A, (rename r φ).foVars = φ.foVars.map r := by
  intro φ
  induction φ with
  | le i j => rfl
  | lab a i => rfl
  | mem i j => rfl
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => simp [rename, foVars, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [rename, foVars, ihφ, ihψ]
  | exFO i φ ih => simp [rename, foVars, ih]
  | exSO i φ ih => simp [rename, foVars, ih]

/-- After shifting all variables up, the variable `0` no longer occurs. -/
lemma zero_notMem_foVars_shiftUp (d : ℕ) (φ : MSO A) :
    0 ∉ (shiftUp (d + 1) φ).foVars := by
  rw [shiftUp, foVars_rename]
  simp

lemma freeFO_rename_subset (r : ℕ → ℕ) :
    ∀ φ : MSO A, (rename r φ).freeFO ⊆ r '' φ.freeFO := by
  intro φ
  induction φ with
  | le i j =>
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨i, Or.inl rfl, rfl⟩
      · exact ⟨j, Or.inr rfl, rfl⟩
  | lab a i => intro x hx; exact ⟨i, rfl, hx.symm ▸ rfl⟩
  | mem i j => intro x hx; exact ⟨i, rfl, hx.symm ▸ rfl⟩
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ =>
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := ihφ hx; exact ⟨y, Or.inl hy, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ihψ hx; exact ⟨y, Or.inr hy, rfl⟩
  | or φ ψ ihφ ihψ =>
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := ihφ hx; exact ⟨y, Or.inl hy, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ihψ hx; exact ⟨y, Or.inr hy, rfl⟩
  | exFO i φ ih =>
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨y, hy, rfl⟩ := ih hx1
      exact ⟨y, ⟨hy, fun h => hx2 (by rw [show y = i from h]; rfl)⟩, rfl⟩
  | exSO i φ ih => exact ih

/-- Renaming a sentence keeps it a sentence. -/
lemma freeFO_rename_eq_empty (r : ℕ → ℕ) {φ : MSO A}
    (h : φ.freeFO = ∅) : (rename r φ).freeFO = ∅ := by
  refine Set.eq_empty_of_subset_empty ?_
  intro x hx
  obtain ⟨y, hy, _⟩ := freeFO_rename_subset r φ hx
  rw [h] at hy
  exact hy.elim

lemma freeFO_shiftUp_eq_empty (d : ℕ) {φ : MSO A} (h : φ.freeFO = ∅) :
    (shiftUp d φ).freeFO = ∅ :=
  freeFO_rename_eq_empty _ h

/-- Shifting the variables of a first-order sentence does not change its
meaning. -/
lemma sat_shiftUp_sentence {φ : MSO A} (hfo : φ.IsFO) (hfree : φ.freeFO = ∅) (d : ℕ)
    (w : List A) (fo fo' : ℕ → ℕ) (so so' : ℕ → Set ℕ) :
    Sat w fo so (shiftUp d φ) ↔ Sat w fo' so' φ := by
  rw [sat_shiftUp]
  exact sat_sentence_congr hfo hfree w _ _ _ _

/-- Every variable occurring in a formula is below its variable bound. -/
lemma mem_foVars_lt_maxVar : ∀ (φ : MSO A) {i : ℕ}, i ∈ φ.foVars → i < MSO.maxVar φ := by
  intro φ
  induction φ with
  | le a b =>
      intro i hi
      have : i = a ∨ i = b := by simpa [foVars] using hi
      rcases this with rfl | rfl <;> simp [maxVar]
  | lab a b => intro i hi; rw [show i = b by simpa [foVars] using hi]; simp [maxVar]
  | mem a b =>
      intro i hi
      rw [show i = a by simpa [foVars] using hi]
      simp [maxVar]
  | not φ ih => intro i hi; exact ih hi
  | and φ ψ ihφ ihψ =>
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact lt_of_lt_of_le (ihφ h) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihψ h) (le_max_right _ _)
  | or φ ψ ihφ ihψ =>
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact lt_of_lt_of_le (ihφ h) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihψ h) (le_max_right _ _)
  | exFO j φ ih =>
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
      · exact lt_of_lt_of_le (ih h) (le_max_right _ _)
  | exSO j φ ih =>
      intro i hi
      exact lt_of_lt_of_le (ih hi) (le_max_right _ _)

/-- After shifting by `d`, every variable of a formula is at least `d`. -/
lemma le_of_mem_foVars_shiftUp (d : ℕ) (φ : MSO A) {i : ℕ} (h : i ∈ (shiftUp d φ).foVars) :
    d ≤ i := by
  rw [shiftUp, foVars_rename] at h
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  omega

/-! ## Finite conjunctions -/

lemma isFO_bigAnd : ∀ (l : List (MSO A)), (∀ φ ∈ l, φ.IsFO) → (bigAnd l).IsFO := by
  intro l
  induction l with
  | nil => intro _; exact trivial
  | cons φ l ih => intro h; exact ⟨h φ (by simp), ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

lemma qrank_bigAnd_le : ∀ (l : List (MSO A)) (n : ℕ), (∀ φ ∈ l, φ.qrank ≤ n) →
    (bigAnd l).qrank ≤ n := by
  intro l
  induction l with
  | nil => intro n _; exact Nat.zero_le n
  | cons φ l ih =>
      intro n h
      have h1 : φ.qrank ≤ n := h φ (by simp)
      have h2 : (bigAnd l).qrank ≤ n := ih n (fun ψ hψ => h ψ (by simp [hψ]))
      exact max_le h1 h2

lemma freeFO_bigAnd_subset {S : Set ℕ} (h0 : (0 : ℕ) ∈ S) :
    ∀ (l : List (MSO A)), (∀ φ ∈ l, φ.freeFO ⊆ S) → (bigAnd l).freeFO ⊆ S := by
  intro l
  induction l with
  | nil =>
      intro _ x hx
      rcases hx with rfl | rfl <;> exact h0
  | cons φ l ih =>
      intro h x hx
      rcases hx with hx | hx
      · exact h φ (by simp) hx
      · exact ih (fun ψ hψ => h ψ (by simp [hψ])) hx

lemma isFO_bigOr : ∀ (l : List (MSO A)), (∀ φ ∈ l, φ.IsFO) → (bigOr l).IsFO := by
  intro l
  induction l with
  | nil => intro _; exact trivial
  | cons φ l ih => intro h; exact ⟨h φ (by simp), ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

end MSO
end Lax314295Proofs.Transducers
