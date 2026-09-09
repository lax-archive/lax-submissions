import Lax485480.WelzlTrees
import Lax214022.Cographs
import Lax195003.WelzlOrdersNeighborhoodSetSystem
import Mathlib.Data.Nat.Log

/-!
---
title: Cographs have logarithmic Welzl trees
type: theorem
---
Every cograph on *n* positive vertices has a spanning tree of crossing number
at most `4 * (ceil(log₂ n) + 1)` for its open-neighborhood set system.

Indeed, a Welzl order determines the path that joins consecutive vertices.
A set crosses exactly the same consecutive pairs in the order as it crosses
edges of this path.  The logarithmic Welzl-order bound for cographs therefore
transfers without loss to spanning trees.

In the terminology of Crespelle and Gambette, the underlying order theorem
is their logarithmic upper bound on cograph contiguity: a neighborhood that
is the union of few intervals has few membership changes along the order.
The path construction records those changes as crossed tree edges.

# Formalization notes

Positivity is assumed because a tree is connected and hence has a vertex;
there is no spanning tree on the empty ground set.  The ceiling logarithm is
`Nat.clog 2 n`, matching the preceding cograph Welzl-order theorem.
-/

namespace Lax485480.CographWelzlTreeUpperBound

open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax214022.Cographs
open Lax485480.WelzlTrees

/-- Every nonempty cograph has an open-neighborhood Welzl tree with at most
four times one plus the ceiling binary logarithm of its order crossings. -/
axiom exists_welzlTree_crossingNumber_le_four_clog_add_one
    (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n)) (hG : IsCograph G) :
    ∃ T : SimpleGraph (Fin n),
      IsWelzlTree (neighborhoodSetSystem G 1) T
        (4 * (Nat.clog 2 n + 1))

end Lax485480.CographWelzlTreeUpperBound
