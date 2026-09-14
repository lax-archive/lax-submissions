/-
**Thresholds of monotone flags.**

The checking automaton of stage 1 of the induction step of the book's snake
lemma verifies that the flags marking the two ends of the window of a piece
never fall back from `true` to `false` along the pair of blocks that carries
them.  Such a flag is therefore the indicator function of a final segment of the
pair, and the cut at which it turns on is the end of the window.  This file
introduces that cut (`Transducers.cutOf`) and its elementary properties.

Nothing here is specific to transducers.
-/
import Mathlib.Tactic

namespace Lax916827Proofs.Transducers

open Classical in
/-- The first position of `[lo, hi)` at which the flag `fl` is on, and `hi` if
there is none. -/
noncomputable def cutOf (fl : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if h : ∃ j, lo ≤ j ∧ j < hi ∧ fl j = true then Nat.find h else hi

variable {fl fl' : ℕ → Bool} {lo hi : ℕ}

lemma cutOf_le_hi : cutOf fl lo hi ≤ hi := by
  classical
  rw [cutOf]
  split
  · rename_i h
    exact le_of_lt (Nat.find_spec h).2.1
  · exact le_refl _

lemma le_cutOf (hlo : lo ≤ hi) : lo ≤ cutOf fl lo hi := by
  classical
  rw [cutOf]
  split
  · rename_i h
    exact (Nat.find_spec h).1
  · exact hlo

lemma cutOf_le_of_true {j : ℕ} (hlo : lo ≤ j) (hhi : j < hi) (hj : fl j = true) :
    cutOf fl lo hi ≤ j := by
  classical
  have h : ∃ j, lo ≤ j ∧ j < hi ∧ fl j = true := ⟨j, hlo, hhi, hj⟩
  rw [cutOf, dif_pos h]
  exact Nat.find_min' h ⟨hlo, hhi, hj⟩

lemma false_of_lt_cutOf {j : ℕ} (hlo : lo ≤ j) (hhi : j < hi) (hj : j < cutOf fl lo hi) :
    fl j = false := by
  by_contra hcon
  simp only [Bool.not_eq_false] at hcon
  have := cutOf_le_of_true hlo hhi hcon
  omega

/-- **A monotone flag is the indicator function of the final segment cut out by
`cutOf`.** -/
lemma cutOf_spec (hmono : ∀ j, lo ≤ j → j + 1 < hi → fl j = true → fl (j + 1) = true)
    {j : ℕ} (hlo : lo ≤ j) (hhi : j < hi) : fl j = true ↔ cutOf fl lo hi ≤ j := by
  classical
  constructor
  · exact fun h => cutOf_le_of_true hlo hhi h
  · intro hle
    have hex : ∃ j, lo ≤ j ∧ j < hi ∧ fl j = true := by
      by_contra hcon
      rw [cutOf, dif_neg hcon] at hle
      omega
    rw [cutOf, dif_pos hex] at hle
    obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
    -- propagate from `Nat.find hex` up to `j`
    have key : ∀ d, Nat.find hex + d < hi → fl (Nat.find hex + d) = true := by
      intro d
      induction d with
      | zero => intro _; simpa using h3
      | succ d ih =>
          intro hd
          have h4 : fl (Nat.find hex + d) = true := ih (by omega)
          have h5 := hmono (Nat.find hex + d) (by omega) (by omega) h4
          rwa [show Nat.find hex + d + 1 = Nat.find hex + (d + 1) from by omega] at h5
    have := key (j - Nat.find hex) (by omega)
    rwa [show Nat.find hex + (j - Nat.find hex) = j from by omega] at this

lemma cutOf_congr (h : ∀ j, lo ≤ j → j < hi → fl j = fl' j) :
    cutOf fl lo hi = cutOf fl' lo hi := by
  classical
  have hiff : (∃ j, lo ≤ j ∧ j < hi ∧ fl j = true) ↔ ∃ j, lo ≤ j ∧ j < hi ∧ fl' j = true := by
    constructor <;> rintro ⟨j, h1, h2, h3⟩ <;> exact ⟨j, h1, h2, by rw [← h j h1 h2] at *; exact h3⟩
  by_cases hex : ∃ j, lo ≤ j ∧ j < hi ∧ fl j = true
  · have hex' := hiff.1 hex
    rw [cutOf, dif_pos hex, cutOf, dif_pos hex']
    refine le_antisymm (Nat.find_le ?_) (Nat.find_le ?_)
    · obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex'
      exact ⟨h1, h2, by rw [h _ h1 h2]; exact h3⟩
    · obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
      exact ⟨h1, h2, by rw [← h _ h1 h2]; exact h3⟩
  · have hex' : ¬ ∃ j, lo ≤ j ∧ j < hi ∧ fl' j = true := fun hc => hex (hiff.2 hc)
    rw [cutOf, dif_neg hex, cutOf, dif_neg hex']

lemma cutOf_le_cutOf (h : ∀ j, lo ≤ j → j < hi → fl' j = true → fl j = true) :
    cutOf fl lo hi ≤ cutOf fl' lo hi := by
  classical
  by_cases hex' : ∃ j, lo ≤ j ∧ j < hi ∧ fl' j = true
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex'
    have hcut : cutOf fl' lo hi = Nat.find hex' := by rw [cutOf, dif_pos hex']
    rw [hcut]
    exact cutOf_le_of_true h1 h2 (h _ h1 h2 h3)
  · have hcut : cutOf fl' lo hi = hi := by rw [cutOf, dif_neg hex']
    rw [hcut]
    exact cutOf_le_hi

lemma cutOf_eq_hi (h : ∀ j, lo ≤ j → j < hi → fl j = false) : cutOf fl lo hi = hi := by
  classical
  rw [cutOf, dif_neg]
  rintro ⟨j, h1, h2, h3⟩
  rw [h j h1 h2] at h3
  exact Bool.noConfusion h3

/-- The flag is on at the cut, unless the cut is the end of the range. -/
lemma true_at_cutOf (h : cutOf fl lo hi < hi) : fl (cutOf fl lo hi) = true := by
  classical
  by_cases hex : ∃ j, lo ≤ j ∧ j < hi ∧ fl j = true
  · have hc : cutOf fl lo hi = Nat.find hex := by rw [cutOf, dif_pos hex]
    rw [hc]
    exact (Nat.find_spec hex).2.2
  · rw [cutOf, dif_neg hex] at h
    omega

/-- If the flag is off below `c` and on from `c` on, the cut is `c`. -/
lemma cutOf_eq_of (c : ℕ) (hlo : lo ≤ c) (hhi : c ≤ hi)
    (hoff : ∀ j, lo ≤ j → j < c → fl j = false)
    (hon : ∀ j, c ≤ j → j < hi → fl j = true) : cutOf fl lo hi = c := by
  rcases Nat.lt_or_ge c hi with hlt | hge
  · refine le_antisymm (cutOf_le_of_true hlo hlt (hon c (le_refl _) hlt)) ?_
    by_contra hcon
    push_neg at hcon
    have h1 : lo ≤ cutOf fl lo hi := le_cutOf (by omega)
    have h2 : fl (cutOf fl lo hi) = true := true_at_cutOf (by omega)
    rw [hoff _ h1 hcon] at h2
    exact Bool.noConfusion h2
  · have hch : c = hi := by omega
    subst hch
    exact cutOf_eq_hi hoff

end Lax916827Proofs.Transducers
