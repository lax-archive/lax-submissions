import Mathlib.Data.Nat.Basic

namespace Lax17Proofs

universe u v w

/-!
# Power-of-two convention for crossbar parameters

Chuzhoy--Tan's crossbar theorem is stated for parameters that are powers of
two.  This definition-only/support module keeps that arithmetic convention
separate from the axiom-bearing crossbar dichotomy contract.
-/

namespace SimpleGraph
namespace CrossbarContract

/-- A natural number is an integral power of two. -/
def IsPowerOfTwo (n : ℕ) : Prop :=
  ∃ r : ℕ, n = 2 ^ r

/-- Powers of two satisfy the crossbar theorem's power-of-two side condition. -/
theorem IsPowerOfTwo.two_pow (r : ℕ) : IsPowerOfTwo (2 ^ r) :=
  ⟨r, rfl⟩

/-- Positive powers of two are at least two. -/
theorem two_le_two_pow {r : ℕ} (hr : 0 < r) : 2 ≤ 2 ^ r := by
  cases r with
  | zero => exact False.elim (Nat.lt_irrefl 0 hr)
  | succ r =>
      exact Nat.le_self_pow (a := 2) (Nat.succ_ne_zero r)

end CrossbarContract
end SimpleGraph

end Lax17Proofs
