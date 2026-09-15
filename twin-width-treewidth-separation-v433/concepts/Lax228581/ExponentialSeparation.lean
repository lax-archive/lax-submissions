import Lax228581.Treewidth
import Lax228581.TwinWidth

/-!
---
title: Twin-width can be exponential in treewidth
type: theorem
---
For every natural number $k$, there is a finite simple graph $G$ whose
treewidth $\mathrm{tw}(G)$ and twin-width $\mathrm{tww}(G)$ satisfy
$$
\mathrm{tw}(G) \le 2k + 4
\qquad\text{and}\qquad
2^k < \mathrm{tww}(G).
$$

# Formalization notes

The graph is quantified over the canonical finite vertex types `Fin n`,
which loses no generality: every finite simple graph is isomorphic to a
graph on some `Fin n`.
-/

namespace Lax228581.ExponentialSeparation

/-- For every `k`, some finite graph has treewidth at most `2 * k + 4` and
twin-width greater than `2 ^ k`. -/
axiom exists_treewidth_le_and_two_pow_lt_twinWidth (k : ℕ) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      Lax228581.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < Lax228581.TwinWidth.twinWidth G

end Lax228581.ExponentialSeparation
