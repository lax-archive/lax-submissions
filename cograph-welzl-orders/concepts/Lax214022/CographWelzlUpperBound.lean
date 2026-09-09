import Lax214022.Cographs
import Lax195003.WelzlOrdersNeighborhoodSetSystem
import Mathlib.Data.Nat.Log

/-!
---
title: Cographs have logarithmic Welzl orders
type: theorem
---
Every cograph on *n* vertices has a Welzl order of crossing number at most
`4 * (ceil(log₂ n) + 1)` for its open-neighborhood set system.

The order is obtained from a cotree by recursively removing a heavy
root-to-leaf path.  The subtrees hanging from that path are ordered first at
join nodes from the root downward and then at union nodes in the reverse
direction.  For a vertex in any one subtree, its neighbors in all the other
subtrees occupy at most two intervals.  Only the subtrees on the vertex's
path through the recursive decomposition matter.  The number of recursive
levels is the Strahler rank of the cotree, which is at most the binary
logarithm of its number of leaves.

# Formalization notes

The ceiling logarithm is `Nat.clog 2 n`, matching the convention in the
Welzl-order submission.  The additive one absorbs the two harmless endpoint
boundaries in the recursive construction.  The statement is valid without a
nonemptiness hypothesis: at `n = 0` the unique order has crossing number zero.
-/

namespace Lax214022.CographWelzlUpperBound

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax214022.Cographs

/-- Every cograph has an open-neighborhood Welzl order with at most four
times one plus the ceiling binary logarithm of its order crossings. -/
axiom exists_welzlOrder_crossingNumber_le_four_clog_add_one
    (n : ℕ) (G : SimpleGraph (Fin n)) (hG : IsCograph G) :
    ∃ π : Equiv.Perm (Fin n),
      IsWelzlOrder (neighborhoodSetSystem G 1) π
        (4 * (Nat.clog 2 n + 1))

end Lax214022.CographWelzlUpperBound
