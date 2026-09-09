import Lax485480.CographWelzlTreeUpperBound
import Lax485480Proofs.OrderPath
import Lax214022.CographWelzlUpperBound

/-!
# Logarithmic Welzl trees for cographs

The logarithmic Welzl order already proved for a cograph is viewed as a
spanning path.  The generic order-path bridge preserves every row's crossing
count exactly.
-/

namespace Lax485480Proofs.CographWelzlTreeUpperBound

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax214022.Cographs
open Lax485480.WelzlTrees
open Lax485480Proofs.OrderPath

noncomputable section

/--
---
conclusion: Lax485480.CographWelzlTreeUpperBound.exists_welzlTree_crossingNumber_le_four_clog_add_one
---
Every nonempty cograph has a spanning Welzl tree with at most
`4 * (ceil(log₂ n) + 1)` crossings per open-neighborhood row.

# Proof strategy

Apply the preceding logarithmic Welzl-order theorem and join consecutive
vertices of its witnessing order.  This graph is a spanning path, hence a
tree, and the order-path bridge identifies its tree crossing number with the
crossing number of the order.

# Attribution

The path construction is the immediate tree form of Welzl's crossing-number
definition; the cograph order bound is imported from lax-214022.
-/
theorem exists_welzlTree_crossingNumber_le_four_clog_add_one
    (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n)) (hG : IsCograph G) :
    ∃ T : SimpleGraph (Fin n),
      IsWelzlTree (neighborhoodSetSystem G 1) T
        (4 * (Nat.clog 2 n + 1)) := by
  obtain ⟨π, hπ⟩ :=
    Lax214022.CographWelzlUpperBound.exists_welzlOrder_crossingNumber_le_four_clog_add_one
      n G hG
  refine ⟨orderPath π, orderPath_isTree hn π, ?_⟩
  rw [treeCrossingNumber_orderPath]
  exact hπ

end

end Lax485480Proofs.CographWelzlTreeUpperBound
