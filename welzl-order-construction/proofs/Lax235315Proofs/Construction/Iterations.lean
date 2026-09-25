import Mathlib.Data.Nat.Log

/-!
The recurrence and round bound from Section 3.1 of the paper.
-/

namespace Lax235315Proofs.Construction.Iterations

/-- A sequence of active-side cardinalities. Every proper round starts above
the loop threshold and satisfies `a' ≤ a/2 + d`. -/
inductive ShrinkingRun (d threshold initial : ℕ) : ℕ → ℕ → Prop
  | base : ShrinkingRun d threshold initial 0 initial
  | step {rounds a a' : ℕ}
      (previous : ShrinkingRun d threshold initial rounds a)
      (large : threshold < a)
      (shrinks : a' ≤ a / 2 + d) :
      ShrinkingRun d threshold initial (rounds + 1) a'

/-- Unfolding `a' ≤ a/2+d` gives the geometric estimate from the paper,
with the geometric tail bounded by `2d`. -/
lemma ShrinkingRun.value_le {d threshold initial rounds a : ℕ}
    (h : ShrinkingRun d threshold initial rounds a) :
    a ≤ initial / 2 ^ rounds + 2 * d := by
  induction h with
  | base => simp
  | @step rounds a a' previous large shrinks ih =>
      calc
        a' ≤ a / 2 + d := shrinks
        _ ≤ (initial / 2 ^ rounds + 2 * d) / 2 + d :=
          Nat.add_le_add_right (Nat.div_le_div_right ih) _
        _ = initial / 2 ^ (rounds + 1) + 2 * d := by
          rw [show 2 * d = d * 2 by omega, Nat.add_mul_div_right _ _ (by omega)]
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
          omega

/-- If `initial ≤ 2^L`, `d,L ≥ 1`, and the loop threshold is `12dL`,
there can be at most `L` reduction rounds. This is the natural-number
counterpart of Theorem 3.1. -/
lemma ShrinkingRun.rounds_le {d initial rounds a L : ℕ}
    (hd : 1 ≤ d) (hL : 1 ≤ L) (hinitial : initial ≤ 2 ^ L)
    (h : ShrinkingRun d (12 * d * L) initial rounds a) :
    rounds ≤ L := by
  induction h with
  | base => omega
  | @step rounds a a' previous large shrinks ih =>
      have hr : rounds ≤ L := ih
      have ha : a ≤ initial / 2 ^ rounds + 2 * d := previous.value_le
      have hne : rounds ≠ L := by
        intro heq
        subst rounds
        have hdiv : initial / 2 ^ L ≤ 1 := by
          apply Nat.div_le_of_le_mul
          simpa using hinitial
        have hthreshold : 1 + 2 * d ≤ 12 * d * L := by
          calc
            1 + 2 * d ≤ 3 * d := by omega
            _ ≤ 12 * d := Nat.mul_le_mul_right d (by omega)
            _ ≤ 12 * d * L := by
              have := Nat.mul_le_mul_left (12 * d) hL
              simpa using this
        omega
      omega

/-- The sharper form used by the crossing induction: the number of rounds
plus the base layer is at most `L`. -/
lemma ShrinkingRun.rounds_succ_le {d initial rounds a L : ℕ}
    (hd : 1 ≤ d) (hL : 1 ≤ L) (hinitial : initial ≤ 2 ^ L)
    (h : ShrinkingRun d (12 * d * L) initial rounds a) :
    rounds + 1 ≤ L := by
  induction h with
  | base => exact hL
  | @step rounds a a' previous large shrinks ih =>
      have ha : a ≤ initial / 2 ^ rounds + 2 * d := previous.value_le
      have hne : rounds + 1 ≠ L := by
        intro heq
        have hpow : 2 ^ rounds * 2 = 2 ^ L := by
          rw [← Nat.pow_succ]
          congr
        have hini : initial ≤ 2 ^ rounds * 2 := by
          rw [hpow]
          exact hinitial
        have hdiv : initial / 2 ^ rounds ≤ 2 :=
          Nat.div_le_of_le_mul hini
        have hthreshold : 2 + 2 * d ≤ 12 * d * L := by
          calc
            2 + 2 * d ≤ 4 * d := by omega
            _ ≤ 12 * d := Nat.mul_le_mul_right d (by omega)
            _ ≤ 12 * d * L := by
              have := Nat.mul_le_mul_left (12 * d) hL
              simpa using this
        omega
      omega

/-- Specialization to the paper's `d=c²` and the ceiling binary logarithm. -/
lemma ShrinkingRun.rounds_le_clog {n c rounds a : ℕ}
    (hc : 1 ≤ c) (hn : 1 < n)
    (h : ShrinkingRun (c ^ 2)
      (12 * c ^ 2 * Nat.clog 2 n) n rounds a) :
    rounds ≤ Nat.clog 2 n := by
  apply h.rounds_le
  · exact Nat.one_le_pow 2 c (by omega)
  · exact Nat.clog_pos (by omega) hn
  · exact Nat.le_pow_clog (by omega) n

lemma ShrinkingRun.rounds_succ_le_clog {n c rounds a : ℕ}
    (hc : 1 ≤ c) (hn : 1 < n)
    (h : ShrinkingRun (c ^ 2)
      (12 * c ^ 2 * Nat.clog 2 n) n rounds a) :
    rounds + 1 ≤ Nat.clog 2 n := by
  apply h.rounds_succ_le
  · exact Nat.one_le_pow 2 c (by omega)
  · exact Nat.clog_pos (by omega) hn
  · exact Nat.le_pow_clog (by omega) n

end Lax235315Proofs.Construction.Iterations
