import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Cardinality and parameter arithmetic for the refined sampler's three output
parts: the initial sample and the two repair phases.
-/

namespace Lax457868Proofs.SamplerSize

/-- The cardinality of a union is bounded by the sum of the two
cardinalities. -/
lemma card_union_le_sum {α : Type*} [DecidableEq α]
    (X Y : Finset α) : (X ∪ Y).card ≤ X.card + Y.card :=
  Finset.card_union_le X Y

/-- The cardinality of a union of three finite sets is bounded by the sum of
their cardinalities. -/
lemma card_union_three_le_sum {α : Type*} [DecidableEq α]
    (X Y Z : Finset α) : (X ∪ Y ∪ Z).card ≤ X.card + Y.card + Z.card := by
  calc
    (X ∪ Y ∪ Z).card ≤ (X ∪ Y).card + Z.card := card_union_le_sum _ _
    _ ≤ X.card + Y.card + Z.card := by
      exact Nat.add_le_add_right (card_union_le_sum X Y) _

/-- The sampler's point budget implies its target cardinality bound: if
`4*c^2*(s+1)*q` fits in a ground set of size `n`, then an initial block of
size `floor(n/(4*c^2))`, followed by at most `q+s*q` repair points, fits in
`ceil(n/(2*c^2))`. -/
theorem sampler_budget_output_bound (n c s q : ℕ)
    (hc : 0 < c)
    (hbudget : 4 * c ^ 2 * (s + 1) * q ≤ n) :
    n / (4 * c ^ 2) + q + s * q ≤ (n + 2 * c ^ 2 - 1) / (2 * c ^ 2) := by
  let d := 2 * c ^ 2
  let D := 4 * c ^ 2
  let extra := (s + 1) * q
  have hd : 0 < d := by dsimp [d]; positivity
  have hbudget' : D * extra ≤ n := by
    calc
      D * extra = 4 * c ^ 2 * (s + 1) * q := by
        dsimp [D, extra]
        ring
      _ ≤ n := hbudget
  have hquot : D * (n / D) ≤ n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self n D
  have hdouble : D * (n / D + extra) ≤ 2 * n := by
    calc
      D * (n / D + extra) = D * (n / D) + D * extra := Nat.mul_add _ _ _
      _ ≤ n + n := Nat.add_le_add hquot hbudget'
      _ = 2 * n := by omega
  have hscaled : d * (n / D + extra) ≤ n := by
    have hmul : 2 * (d * (n / D + extra)) ≤ 2 * n := by
      calc
        2 * (d * (n / D + extra)) = D * (n / D + extra) := by
          dsimp [d, D]
          ring
        _ ≤ 2 * n := hdouble
    omega
  have hceil : n / D + extra ≤ (n + d - 1) / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    calc
      (n / D + extra) * d = d * (n / D + extra) := Nat.mul_comm _ _
      _ ≤ n := hscaled
      _ ≤ n + d - 1 := by omega
  calc
    n / D + q + s * q = n / D + extra := by
      dsimp [extra]
      ring
    _ ≤ (n + d - 1) / d := hceil
    _ = (n + 2 * c ^ 2 - 1) / (2 * c ^ 2) := by rfl

/-- If the phase-two and phase-three additions respect their respective
budgets, their union with the initial sample respects the sampler's final
cardinality bound. -/
theorem sampler_union_card_bound {α : Type*} [DecidableEq α]
    (initial phaseTwo phaseThree : Finset α) (n c s q : ℕ)
    (hc : 0 < c)
    (hbudget : 4 * c ^ 2 * (s + 1) * q ≤ n)
    (hinitial : initial.card = n / (4 * c ^ 2))
    (hphaseTwo : phaseTwo.card ≤ q)
    (hphaseThree : phaseThree.card ≤ s * q) :
    (initial ∪ phaseTwo ∪ phaseThree).card ≤
      (n + 2 * c ^ 2 - 1) / (2 * c ^ 2) := by
  calc
    (initial ∪ phaseTwo ∪ phaseThree).card ≤
        initial.card + phaseTwo.card + phaseThree.card :=
      card_union_three_le_sum initial phaseTwo phaseThree
    _ ≤ n / (4 * c ^ 2) + q + s * q := by omega
    _ ≤ (n + 2 * c ^ 2 - 1) / (2 * c ^ 2) :=
      sampler_budget_output_bound n c s q hc hbudget

end Lax457868Proofs.SamplerSize
