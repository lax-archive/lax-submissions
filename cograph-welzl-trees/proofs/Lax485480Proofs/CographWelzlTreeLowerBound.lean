import Lax485480.CographWelzlTreeLowerBound
import Lax485480Proofs.TreeOrder
import Lax214022.CographWelzlLowerBound

/-!
# Cographs can require logarithmic Welzl trees

The cograph order obstruction from lax-214022 transfers to trees through
the factor-two tree-to-order linearization theorem.
-/

namespace Lax485480Proofs.CographWelzlTreeLowerBound

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax214022.Cographs
open Lax485480.WelzlTrees
open Lax485480Proofs.TreeOrder

noncomputable section

/--
---
conclusion: Lax485480.CographWelzlTreeLowerBound.exists_cograph_requiring_treeCrossingNumber_at_least
---
There are cographs on between `3^k` and `4^k` vertices for which every
Welzl tree has crossing number at least `ceil(k/2)`.

# Proof strategy

Use the cograph from the logarithmic Welzl-order lower bound.  Given any
spanning tree of crossing number `c`, repeatedly delete a leaf and reinsert
it beside its unique neighbor to obtain an order of crossing number at most
`2c`.  The witness requires at least `k` order crossings, so `k ≤ 2c`,
which is equivalent over the naturals to `ceil(k/2) ≤ c`.

# Attribution

Crespelle and Gambette proved the logarithmic contiguity lower bound for
cographs with complete binary cotrees.  The explicit order witnesses used
here are imported from lax-214022.  The leaf-removal linearization is the
standard depth-first factor-two conversion from tree cuts to a linear
layout, and upgrades their order phenomenon to arbitrary spanning trees.
-/
theorem exists_cograph_requiring_treeCrossingNumber_at_least (k : ℕ) :
    ∃ n : ℕ, 3 ^ k ≤ n ∧ n ≤ 4 ^ k ∧
      ∃ G : SimpleGraph (Fin n), IsCograph G ∧
        ∀ T : SimpleGraph (Fin n), T.IsTree →
          (k + 1) / 2 ≤
            treeCrossingNumber (neighborhoodSetSystem G 1) T := by
  obtain ⟨n, hn₃, hn₄, G, hG, horder⟩ :=
    Lax214022.CographWelzlLowerBound.exists_cograph_requiring_crossingNumber_at_least k
  refine ⟨n, hn₃, hn₄, G, hG, ?_⟩
  intro T hT
  obtain ⟨π, hπ⟩ := exists_order_crossingNumber_le_two_mul
    (neighborhoodSetSystem G 1) T hT
  have hk := (horder π).trans hπ
  omega

end

end Lax485480Proofs.CographWelzlTreeLowerBound
