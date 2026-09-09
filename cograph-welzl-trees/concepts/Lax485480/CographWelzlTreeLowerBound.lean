import Lax485480.WelzlTrees
import Lax214022.Cographs
import Lax195003.WelzlOrdersNeighborhoodSetSystem

/-!
---
title: Cographs can require logarithmic Welzl trees
type: theorem
---
For every nonnegative integer *k*, there is a cograph on at least `3^k` and
at most `4^k` vertices such that every spanning tree has crossing number at
least `ceil(k/2)` for the open-neighborhood set system.

The witnesses are the same recursively constructed cographs that require
*k* crossings in every Welzl order.  Every spanning tree of crossing number
*c* can be linearized with crossing number at most `2c`: delete leaves one at
a time and, in reverse, insert each leaf beside its tree neighbor.  Inserting
a leaf changes a row only when its incident tree edge is crossed, and then
adds at most two crossings.  Hence an order lower bound of *k* gives a tree
lower bound of `ceil(k/2)`.

# Formalization notes

The ceiling is expressed in natural arithmetic as `(k + 1) / 2`.  The two
exponential inequalities retain the rounded-logarithm-free size convention
of the preceding Welzl-order lower bound.
-/

namespace Lax485480.CographWelzlTreeLowerBound

open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax214022.Cographs
open Lax485480.WelzlTrees

/-- There are cographs of order at most `4^k` on which every spanning tree
has crossing number at least `ceil(k/2)`. -/
axiom exists_cograph_requiring_treeCrossingNumber_at_least (k : ℕ) :
    ∃ n : ℕ, 3 ^ k ≤ n ∧ n ≤ 4 ^ k ∧
      ∃ G : SimpleGraph (Fin n), IsCograph G ∧
        ∀ T : SimpleGraph (Fin n), T.IsTree →
          (k + 1) / 2 ≤
            treeCrossingNumber (neighborhoodSetSystem G 1) T

end Lax485480.CographWelzlTreeLowerBound
