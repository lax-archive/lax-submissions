import Lax235315.SequenceCrossings
import Lax235315.TwinInsertion
import Lax235315.NearTwinStability
import Mathlib.Tactic

namespace Lax235315Proofs.Crossings

open Lax235315.SequenceCrossings

private lemma edge_change_bound (a b c d : Bool) :
    (if a = b then 0 else 1) ≤
      (if c = d then 0 else 1) + (if a = c then 0 else 1) +
        (if b = d then 0 else 1) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private def bitChange (a b : Bool) : ℕ := if a = b then 0 else 1

private theorem crossings_le_add_head_change (xs ys : List Bool)
    (h : xs.length = ys.length) :
    crossings xs ≤ crossings ys +
      (match xs, ys with
       | a :: _, b :: _ => bitChange a b
       | _, _ => 0) + 2 * hamming xs.tail ys.tail := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp_all [crossings, hamming]
  | cons a xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp [crossings, hamming]
          | cons c ys =>
              cases ys <;> simp_all [crossings, hamming]
      | cons b tail =>
          cases ys with
          | nil => simp at h
          | cons c ys =>
              cases ys with
              | nil => simp at h
              | cons d tailY =>
                  have htail : (b :: tail).length = (d :: tailY).length := by
                    simpa using h
                  have hi := ih (ys := d :: tailY) htail
                  have he := edge_change_bound a b c d
                  simp only [List.tail_cons, crossings, hamming, bitChange] at hi ⊢
                  omega

/--
---
conclusion: Lax235315.TwinInsertion.crossings_duplicate
---
Duplicating a membership bit beside itself preserves the crossing count.

# Proof strategy
Induct on the prefix. The duplicate creates no new change, and the crossing
from the preceding bit to the duplicate is the same as the crossing to the
original bit.

# Attribution
The statement is the adjacent-twin crossing observation used in Lemma 2.1 of
Dreier and Kuske, *Fast exact algorithms via modular decomposition*.
-/
theorem crossings_duplicate (pre post : List Bool) (b : Bool) :
    crossings (pre ++ b :: b :: post) =
      crossings (pre ++ b :: post) := by
  induction pre with
  | nil => simp [crossings]
  | cons a pre ih =>
      cases pre with
      | nil => simp [crossings]
      | cons c rest =>
          simp only [List.cons_append, crossings]
          have ih' : crossings (c :: (rest ++ b :: b :: post)) =
              crossings (c :: (rest ++ b :: post)) := by
            simpa only [List.cons_append] using ih
          rw [ih']

/--
---
conclusion: Lax235315.NearTwinStability.crossings_le_add_twice_hamming
---
Changing membership at *k* positions changes the crossing count by at most
*2k*.

# Proof strategy
A strengthened induction charges the first position once and each remaining
position at most twice. Each edge changes only when one of its endpoint bits
changes, so every changed position is charged at most twice overall.

# Attribution
This is the elementary membership-sequence estimate in Lemma 2.2 of Dreier
and Kuske, *Fast exact algorithms via modular decomposition*.
-/
theorem crossings_le_add_twice_hamming (xs ys : List Bool)
    (h : xs.length = ys.length) :
    crossings xs ≤ crossings ys + 2 * hamming xs ys := by
  have h' := crossings_le_add_head_change xs ys h
  cases xs with
  | nil =>
      cases ys with
      | nil => simp [crossings, hamming]
      | cons b ys => simp at h
  | cons a tail =>
      cases ys with
      | nil => simp at h
      | cons b tailY =>
          have h'' : crossings (a :: tail) ≤
              crossings (b :: tailY) + bitChange a b +
                2 * hamming tail tailY := by
            simpa [hamming, bitChange] using h'
          have hgoal : crossings (a :: tail) ≤
              crossings (b :: tailY) + 2 * bitChange a b +
                2 * hamming tail tailY := by omega
          change crossings (a :: tail) ≤ crossings (b :: tailY) +
            2 * (bitChange a b + hamming tail tailY)
          calc
            crossings (a :: tail) ≤
                crossings (b :: tailY) + bitChange a b +
                  2 * hamming tail tailY := h''
            _ ≤ crossings (b :: tailY) + 2 * bitChange a b +
                  2 * hamming tail tailY := by omega
            _ = crossings (b :: tailY) +
                  2 * (bitChange a b + hamming tail tailY) := by omega

end Lax235315Proofs.Crossings
