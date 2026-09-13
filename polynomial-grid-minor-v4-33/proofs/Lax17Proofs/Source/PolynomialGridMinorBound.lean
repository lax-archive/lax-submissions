import Mathlib.Data.Nat.Log

namespace Lax17Proofs

universe u v w

/-!
# Polynomial grid-minor threshold

This definition-only file contains the natural-number threshold expression used
in the polynomial grid-minor theorem.  It is separate from the contract theorem
so proof files can refer to the bound without importing the final theorem
wrapper.
-/

namespace SimpleGraph

/-- The explicit natural-number treewidth threshold
`c1 * g^9 * (log_2 g)^c2` used to state the polynomial grid-minor theorem. -/
def polynomialGridMinorTreewidthBound (c1 c2 g : ℕ) : ℕ :=
  c1 * g ^ 9 * (Nat.log 2 g) ^ c2

/-- The weaker degree-ten natural-number treewidth threshold used as a
compatibility target for the `k^10 polylog k` form of the grid-minor theorem. -/
def polynomialGridMinorTreewidthBound10 (c1 c2 g : ℕ) : ℕ :=
  c1 * g ^ 10 * (Nat.log 2 g) ^ c2

end SimpleGraph

end Lax17Proofs
