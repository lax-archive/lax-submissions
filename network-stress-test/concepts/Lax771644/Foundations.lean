import Mathlib.Data.Nat.Notation

/-!
---
title: The benchmark ladder
type: definition
---
Every claim in this submission is a rung of one ladder: for natural numbers
$a$ and $b$, the assertion that divisibility by $2^a$ implies divisibility by
$2^b$. The mathematics is deliberately trivial. It exists only so that this
submission's *dependency graph* can be wired into any shape at all while every
proof still genuinely applies the statements it declares as assumptions.

# Formalization notes

`Stage k n` is plain divisibility, `2 ^ k ∣ n`, and `Descent a b` is the
statement shape every axiom of this submission uses. Because `Descent a b`
holds whenever `b ≤ a`, a proof of one rung can be assembled from *any*
descending sequence of other rungs. That is what lets the proof network of this
submission take on arbitrary shapes — long chains, cycles, wide fans — without
any statement being false or any proof pretending to use an assumption it does
not.
-/

namespace Lax771644.Foundations

/-- `Stage k n` says that `n` is divisible by `2 ^ k`. -/
def Stage (k n : ℕ) : Prop := 2 ^ k ∣ n

/-- `Descent a b` is the one statement shape this submission uses: every natural
number divisible by `2 ^ a` is divisible by `2 ^ b`. -/
def Descent (a b : ℕ) : Prop := ∀ n : ℕ, Stage a n → Stage b n

end Lax771644.Foundations
