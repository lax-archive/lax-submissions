import Lax214022.Cographs
import Lax195003.WelzlOrdersNeighborhoodSetSystem

/-!
---
title: Cographs can require logarithmic Welzl orders
type: theorem
---
For every nonnegative integer *k*, there is a cograph on at least `3^k` and
at most `4^k` vertices such that every vertex order has crossing number at
least *k* for the open-neighborhood set system.  In particular, these graphs
require at least one half of the binary logarithm of their order.

The witnesses are the underlying graphs of the transitive closures of
complete rooted ternary trees.  One recursive step places a universal root
over three disjoint copies of the preceding graph.  In cotree language this
adds a join node and a union node, so every two new cotree levels force one
new crossing.

# Formalization notes

The two exponential inequalities state the logarithmic relation without
introducing rounded real logarithms.  The theorem uses the registered
crossing number directly, at radius one.  Thus it asserts a lower bound for
every permutation, rather than merely exhibiting one order with a large
crossing number.
-/

namespace Lax214022.CographWelzlLowerBound

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax214022.Cographs

/-- There are cographs of order at most `4^k` on which every Welzl order has
crossing number at least `k`. -/
axiom exists_cograph_requiring_crossingNumber_at_least (k : ℕ) :
    ∃ n : ℕ, 3 ^ k ≤ n ∧ n ≤ 4 ^ k ∧
      ∃ G : SimpleGraph (Fin n), IsCograph G ∧
        ∀ π : Equiv.Perm (Fin n),
          k ≤ crossingNumber (neighborhoodSetSystem G 1) π

end Lax214022.CographWelzlLowerBound
