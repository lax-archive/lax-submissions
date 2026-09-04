import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax48.TwinWidth
import Lax65.FeedbackVertexSet

/-!
---
title: Twin-width can be exponential in treewidth
type: theorem
---
For every real $0 < \varepsilon \le 1/2$ and integer $t > 1/\varepsilon$,
there is a graph $G_{t,\varepsilon}$ with a feedback vertex set of size $t$
and $\operatorname{tww}(G_{t,\varepsilon}) > 2^{(1-\varepsilon)t}$.

# Formalization notes

The graph is quantified over the canonical finite vertex types `Fin n`, which
loses no generality: every finite simple graph is isomorphic to a graph on
some `Fin n`. Twin-width is the parameter of the prerequisite submission.
-/

namespace Lax65.ExponentialSeparation

open Lax48.TwinWidth Lax65.FeedbackVertexSet

/-- For every real `0 < ε ≤ 1/2` and integer `t > 1/ε`, some finite graph has
a feedback vertex set of size `t` and twin-width greater than
`2 ^ ((1 - ε) t)`. -/
axiom exists_feedbackVertexSet_and_two_rpow_lt_twinWidth
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1 / 2) (t : ℕ) (ht : 1 / ε < t) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      HasFeedbackVertexSetOfSize G t ∧
        (2 : ℝ) ^ ((1 - ε) * t) < twinWidth G

end Lax65.ExponentialSeparation
