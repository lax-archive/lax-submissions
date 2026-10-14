import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
Finite weighted charging for the one-inclusion argument. The out-degree cap
is assumed; existence of the orientation and the probability coupling are
separate obligations.
-/

namespace Lax457868Proofs.SamplerCharging

/-- Charge each directed edge to its tail. If every tail has at most `d`
outgoing edges, the total charge using twice the smaller endpoint weight is
at most twice `d` times the total vertex weight. -/
lemma weighted_tail_charge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (a : V → ℕ) (d : ℕ)
    (hout : ∀ v, (E.filter fun e => e.1 = v).card ≤ d) :
    (∑ e ∈ E, 2 * min (a e.1) (a e.2)) ≤
      2 * d * (∑ v, a v) := by
  classical
  let charge : V × V → ℕ := fun e => 2 * min (a e.1) (a e.2)
  have hfiber : (∑ e ∈ E, charge e) =
      ∑ v, ∑ e ∈ E.filter (fun e => e.1 = v), charge e := by
    simpa [charge] using
      (Finset.sum_fiberwise_eq_sum_filter E Finset.univ Prod.fst charge).symm
  have htail (v : V) :
      (∑ e ∈ E.filter (fun e => e.1 = v), charge e) ≤ 2 * d * a v := by
    calc
      (∑ e ∈ E.filter (fun e => e.1 = v), charge e) ≤
          ∑ e ∈ E.filter (fun e => e.1 = v), 2 * a v := by
        apply Finset.sum_le_sum
        intro e he
        have htail : e.1 = v := (Finset.mem_filter.mp he).2
        dsimp [charge]
        rw [htail]
        exact Nat.mul_le_mul_left 2 (Nat.min_le_left _ _)
      _ = (E.filter (fun e => e.1 = v)).card * (2 * a v) := by simp
      _ ≤ d * (2 * a v) := Nat.mul_le_mul_right _ (hout v)
      _ = 2 * d * a v := by ring
  calc
    (∑ e ∈ E, 2 * min (a e.1) (a e.2)) =
        ∑ v, ∑ e ∈ E.filter (fun e => e.1 = v), charge e := by
          simpa [charge] using hfiber
    _ ≤ ∑ v, 2 * d * a v := Finset.sum_le_sum fun v _ => htail v
    _ = 2 * d * (∑ v, a v) := by simp [Finset.mul_sum]

/-- For two nonnegative integer class sizes, the expected merge charge
`2*x*y/(x+y)` is at most twice the smaller class size, in denominator-cleared
form. -/
lemma twice_mul_le_twice_min_mul_add (x y : ℕ) :
    2 * x * y ≤ 2 * min x y * (x + y) := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy]
    nlinarith
  · have hyx : y ≤ x := by omega
    rw [min_eq_right hyx]
    nlinarith

end Lax457868Proofs.SamplerCharging
