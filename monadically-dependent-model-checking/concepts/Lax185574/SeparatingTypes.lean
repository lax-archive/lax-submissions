import Lax185574.Colorings
import Lax185574.FirstOrderTypes
import Lax185574.GraphBalls

/-!
---
title: Few types far from a parameter set
type: lemma
---
For every q, k, c ∈ ℕ there are numbers r = r(q) and T = T(q, k, c)
with the following property. Let H be a graph expanded by at most c
unary predicates and U ⊆ V(H). Consider the set

  F ≔ { a ∈ V(H) : dist^H(a, U) > r }

of vertices that are far from U. Then |Types^H_{k,q}(F/U)| ≤ T(q, k, c).

# Formalization notes

The radius r is quantified after q and before k and c, and T after
q, k and c. In particular neither depends on the graph or on |U|. An
expansion by at most c unary predicates is an expansion by exactly c
color sets, some of which may be empty, as in `Colorings.expansion`.
The graph is finite, which is the case in which the lemma is used. The
distance is that of the graph H, which is also the distance in the
Gaifman graph of the expansion. The far set F is the complement of
the ball Ball^H_r[U] of `GraphBalls.graphBall`, so a vertex lies in F if
no walk of length at most r joins a vertex of U to it. If U is empty, F
is the whole vertex set.
-/

namespace Lax185574.SeparatingTypes

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.FirstOrderTypes Lax185574.GraphBalls Lax185574.Colorings

universe z

/-- **Few types far from a parameter set.** In a graph with `c` unary
predicates, the `k`-tuples of vertices at distance more than `r(q)` from
`U` realize at most `T(q, k, c)` types of quantifier rank `q` over
`U`. -/
axiom typeCountOver_far_le (q : ℕ) :
    ∃ r : ℕ, ∀ k c : ℕ, ∃ T : ℕ,
      ∀ (V : Type z) [Finite V] (G : SimpleGraph V) (colors : Fin c → Set V)
        (U : Set V),
        @typeCountOver (withColors Language.graph c) V (expansion G colors) k q
            (graphBall G r U)ᶜ U ≤ T

end Lax185574.SeparatingTypes
